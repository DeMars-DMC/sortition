// Sortition using normal int

package main

import (
	"bytes"
	"crypto/rand"
	"encoding/binary"
	"fmt"
	"io"
	"math"
	"strconv"

	"golang.org/x/crypto/sha3"

	"github.com/yahoo/coname/ed25519/edwards25519"
	"github.com/yahoo/coname/ed25519/extra25519"
)

/**
 * [const description]
 * @param  {[type]} [PublicKeySize=32	SecretKeySize                 = 64	Size             = 32	intermediateSize = 32	ProofSize        = 32 + 32 + intermediateSize)func GenerateKey(rnd io.Reader) (pk []byte, sk *[SecretKeySize]byte, err error] [description]
 * @return {[type]}                                 [description]
 */
// tau controls the election of validators

const (
	PublicKeySize    = 32
	SecretKeySize    = 64
	Size             = 32
	intermediateSize = 32
	ProofSize        = 32 + 32 + intermediateSize
	W                = 10000000000
	tau              = 45010000
)

// GenerateKey creates a public/private key pair. rnd is used for randomness.
// If it is nil, `crypto/rand` is used.
func GenerateKey(rnd io.Reader) (pk []byte, sk *[SecretKeySize]byte, err error) {
	if rnd == nil {
		rnd = rand.Reader
	}
	sk = new([SecretKeySize]byte)
	_, err = io.ReadFull(rnd, sk[:32])
	if err != nil {
		return nil, nil, err
	}
	x, _ := expandSecret(sk)

	var pkP edwards25519.ExtendedGroupElement
	edwards25519.GeScalarMultBase(&pkP, x)
	var pkBytes [PublicKeySize]byte
	pkP.ToBytes(&pkBytes)

	copy(sk[32:], pkBytes[:])
	return pkBytes[:], sk, err
}

func expandSecret(sk *[SecretKeySize]byte) (x, skhr *[32]byte) {
	x, skhr = new([32]byte), new([32]byte)
	hash := sha3.NewShake256()
	hash.Write(sk[:32])
	hash.Read(x[:])
	hash.Read(skhr[:])
	x[0] &= 248
	x[31] &= 127
	x[31] |= 64
	return
}

func Compute(m []byte, sk *[SecretKeySize]byte) []byte {
	x, _ := expandSecret(sk)
	var ii edwards25519.ExtendedGroupElement
	var iiB [32]byte
	edwards25519.GeScalarMult(&ii, x, hashToCurve(m))
	ii.ToBytes(&iiB)

	hash := sha3.NewShake256()
	hash.Write(iiB[:]) // const length: Size
	hash.Write(m)
	var vrf [Size]byte
	hash.Read(vrf[:])
	return vrf[:]
}

func hashToCurve(m []byte) *edwards25519.ExtendedGroupElement {
	// H(n) = (f(h(n))^8)
	var hmb [32]byte
	sha3.ShakeSum256(hmb[:], m)
	var hm edwards25519.ExtendedGroupElement
	extra25519.HashToEdwards(&hm, &hmb)
	edwards25519.GeDouble(&hm, &hm)
	edwards25519.GeDouble(&hm, &hm)
	edwards25519.GeDouble(&hm, &hm)
	return &hm
}

// Prove returns the vrf value and a proof such that Verify(pk, m, vrf, proof)
// == true. The vrf value is the same as returned by Compute(m, sk).
func Prove(m []byte, sk *[SecretKeySize]byte) (vrf, proof []byte) {
	x, skhr := expandSecret(sk)
	var cH, rH [64]byte
	var r, c, minusC, t, grB, hrB, iiB [32]byte
	var ii, gr, hr edwards25519.ExtendedGroupElement

	hm := hashToCurve(m)
	edwards25519.GeScalarMult(&ii, x, hm)
	ii.ToBytes(&iiB)

	hash := sha3.NewShake256()
	hash.Write(skhr[:])
	hash.Write(sk[32:]) // public key, as in ed25519
	hash.Write(m)
	hash.Read(rH[:])
	hash.Reset()
	edwards25519.ScReduce(&r, &rH)

	edwards25519.GeScalarMultBase(&gr, &r)
	edwards25519.GeScalarMult(&hr, &r, hm)
	gr.ToBytes(&grB)
	hr.ToBytes(&hrB)

	hash.Write(grB[:])
	hash.Write(hrB[:])
	hash.Write(m)
	hash.Read(cH[:])
	hash.Reset()
	edwards25519.ScReduce(&c, &cH)

	edwards25519.ScNeg(&minusC, &c)
	edwards25519.ScMulAdd(&t, x, &minusC, &r)

	proof = make([]byte, ProofSize)
	copy(proof[:32], c[:])
	copy(proof[32:64], t[:])
	copy(proof[64:96], iiB[:])

	hash.Write(iiB[:]) // const length: Size
	hash.Write(m)
	vrf = make([]byte, Size)
	hash.Read(vrf[:])
	return
}

// Verify returns true iff vrf=Compute(m, sk) for the sk that corresponds to pk.
func Verify(pkBytes, m, vrfBytes, proof []byte) bool {
	fmt.Sprintln("in Verify")
	if len(proof) != ProofSize || len(vrfBytes) != Size || len(pkBytes) != PublicKeySize {
		return false
	}
	var pk, c, cRef, t, vrf, iiB, ABytes, BBytes [32]byte
	copy(vrf[:], vrfBytes)
	copy(pk[:], pkBytes)
	copy(c[:32], proof[:32])
	copy(t[:32], proof[32:64])
	copy(iiB[:], proof[64:96])

	hash := sha3.NewShake256()
	hash.Write(iiB[:]) // const length
	hash.Write(m)
	var hCheck [Size]byte
	hash.Read(hCheck[:])
	if !bytes.Equal(hCheck[:], vrf[:]) {
		return false
	}
	hash.Reset()

	var P, B, ii, iic edwards25519.ExtendedGroupElement
	var A, hmtP, iicP edwards25519.ProjectiveGroupElement
	if !P.FromBytesBaseGroup(&pk) {
		return false
	}
	if !ii.FromBytesBaseGroup(&iiB) {
		return false
	}
	edwards25519.GeDoubleScalarMultVartime(&A, &c, &P, &t)
	A.ToBytes(&ABytes)

	hm := hashToCurve(m)
	edwards25519.GeDoubleScalarMultVartime(&hmtP, &t, hm, &[32]byte{})
	edwards25519.GeDoubleScalarMultVartime(&iicP, &c, &ii, &[32]byte{})
	iicP.ToExtended(&iic)
	hmtP.ToExtended(&B)
	edwards25519.GeAdd(&B, &B, &iic)
	B.ToBytes(&BBytes)

	var cH [64]byte
	hash.Write(ABytes[:]) // const length
	hash.Write(BBytes[:]) // const length
	hash.Write(m)
	hash.Read(cH[:])
	edwards25519.ScReduce(&cRef, &cH)
	return cRef == c
}

// factorial(n)
func factorial(n float64) float64 {
	if n <= 1 {
		return 1
	} else {
		return n * factorial(n-1)
	}
}

// nCk, trivial
func combination(k float64, n float64) float64 {
	combWX := float64(factorial(n) /
		factorial(k) /
		factorial(n-k))
	return combWX
}

// nCk, optimization 1
func combination2(k int64, n int64) int64 {
	var comb int64
	comb = 1
	if k > n-k {
		k = n - k
	}
	var j int64
	for j = 1; j <= k; j, n = j-1, n+1 {
		if n%j == 0 {
			comb *= (n / j)
		} else if comb%j == 0 {
			comb = comb / j * n
		} else {
			comb = comb * n / j
		}
	}
	return comb
}

// nCk, optimization 2
func combination3(k float64, n float64) float64 {
	if k > n {
		return 0.0
	}
	if k*2 > n {
		k = n - k
	}
	if k == 0 {
		return 1.0
	}

	result := n
	for i := 2.0; i <= k; i++ {
		result *= (n - i + 1)
		result /= i
	}
	return result
}

// nCk, optimization 3
func combOpt(k float64, n float64, p float64) float64 {
	if k == 0 {
		return 1.0
	}
	if k > n {
		return 0.0
	}
	if k*2 > n {
		k = n - k
		p = 1.0 - p
	}

	result := n * p
	for i := 2.0; i <= k; i++ {
		result *= (n - i + 1)
		result /= i
		result *= p
	}
	return result
}

// nCk, optimization 4
func combOpt2(k float64, n float64, p float64) float64 {
	// fmt.Println("Optv2")
	var large bool
	if k == 0 {
		return 1.0
	}
	if k > n {
		return 0.0
	}
	if k*2 > n {
		large = true
		k = n - k
		p = 1.0 - p
	}

	result := n * p * (1 - p)
	for i := 2.0; i <= k; i++ {
		result *= (n - i + 1)
		result /= i
		result *= p
		result *= (1.0 - p)
	}
	if large {
		pK := math.Pow(p, float64(2*k-n))
		return result * pK
	} else {
		minuspK := math.Pow(1.0-p, float64(n-2*k))
		return result * minuspK
	}
	return result
}

// nCk, optimization 5
func combOpt3(k float64, n float64, p float64) float64 {
	var large bool
	if k == 0 {
		return 1.0
	}
	if k > n {
		return 0.0
	}
	if k*2 > n {
		large = true
		k = n - k
		p = 1.0 - p
	}

	result := n * p * (1.0 - p) * (1.0 - p) * (1.0 - p) * (1.0 - p)
	fmt.Println("Result1 = ", result)
	for i := 2.0; i <= k; i++ {
		result *= (n - i + 1)
		result /= i
		result *= p
		result *= (1.0 - p) * (1.0 - p) * (1.0 - p) * (1.0 - p)
	}
	fmt.Println("Resultk = ", result)
	if large {
		pK := math.Pow(p, float64(2*k-n))
		return result * pK
	} else {
		if (n - 5*k) > 0 {
			minuspK := math.Pow(1.0-p, float64(n-5*k))
			fmt.Println("n - 5k = ", (n - 5*k))
			fmt.Println("(1-p)^n-5k = ", minuspK)
			fmt.Println("Result = ", result)
			return result * minuspK
		} else {
			minuspK := math.Pow(1.0-p, float64(-1*(n-4*k)))
			return result / minuspK
		}
	}
	return result
}

func binomial(k int, w int, p float64) float64 {
	combWX := combination3(float64(k), float64(w))
	pK := math.Pow(p, float64(k))
	qWK := math.Pow(1.0-p, float64(w-k))
	return combWX * pK * qWK
}

// Optimized binomial coefficients using combOpt
func binomialOpt(k int, w int, p float64) float64 {
	combWX := combOpt(float64(k), float64(w), p)
	if k*2 > w {
		pK := math.Pow(p, float64(k))
		return combWX * pK
	} else {
		qWK := math.Pow(1.0-p, float64(w-k))
		return combWX * qWK
	}
}

// Optimized binomial coefficients using combOpt2
func binomialOpt2(k int, w int, p float64) float64 {
	combWX := combOpt2(float64(k), float64(w), p)
	return combWX
}

// n - sample size, p - fraction of malicious nodes in complete set, g - fraction of uncorrupted nodes in sample
func sampling(n float64, p float64, g float64) float64 {
	chance := 0.0
	for k := n * g; k <= n; k++ {
		chance += math.Pow(p, k) * math.Pow(1-p, n-k) * combination3(k, n)
	}
	return chance
}

func binomialsum(j int, w int, p float64) float64 {
	sum := 0.0
	for k := 0; k <= j; k++ {
		sum += binomialOpt(k, w, p)
	}
	return sum
}

func Sortition(sk *[SecretKeySize]byte, seed int, role int, OwnBalance int) ([]byte, []byte, []byte, int) {
	seedb := []byte(strconv.Itoa(seed))
	roleb := []byte(strconv.Itoa(role))
	message := append(seedb, roleb...)
	hash, proof := Prove(message, sk)
	hashInt := binary.BigEndian.Uint64(hash)
	hashFloat := float64(hashInt)
	p := float64(float64(tau) / float64(W))
	j := 0

	value := hashFloat / math.Pow(2, float64(len(hash)*8))
	fmt.Println("Value in sortition() = ", value)
	fmt.Println(binomialsum(j, OwnBalance, p), " ", binomialsum(j+1, OwnBalance, p))
	for (value < binomialsum(j, OwnBalance, p) || value >= binomialsum(j+1, OwnBalance, p)) && binomialsum(j, OwnBalance, p) != binomialsum(j+1, OwnBalance, p) {
		fmt.Println("Obtained vote for zone [", binomialsum(j, OwnBalance, p), ",", binomialsum(j+1, OwnBalance, p), ")")
		if binomialsum(j, OwnBalance, p) > 1 || binomialsum(j+1, OwnBalance, p) > 1 {
			break
		}
		j++
	}

	return hash, proof, message, j
}

func VerifySort(pk []byte, hash []byte, proof []byte, seed int, role int, OwnBalance int) int {
	seedb := []byte(strconv.Itoa(seed))
	roleb := []byte(strconv.Itoa(role))
	message := append(seedb, roleb...)
	check := Verify(pk, message, hash, proof)
	if check == false {
		return 0
	}
	hashInt := binary.BigEndian.Uint64(hash)
	hashFloat := float64(hashInt)
	p := float64(float64(tau) / float64(W))
	j := 0

	value := hashFloat / math.Pow(2, float64(len(hash)*8))
	for value < binomialsum(j, OwnBalance, p) || value >= binomialsum(j+1, OwnBalance, p) {
		j++
	}

	return j
}

func main() {
	_, sk, _ := GenerateKey(nil)
	bal2 := 10000
	_, _, _, count2 := Sortition(sk, 2, 1, bal2)

	fmt.Println("Verified, Votes = ", count2, "/", bal2)
}
