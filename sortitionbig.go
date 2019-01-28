// Sortition using big integer, based on VRFs

package main

import (
	"bytes"
	"crypto/rand"
	"encoding/binary"
	"fmt"
	"io"
	"math"
	"math/big"
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
	tau              = 160000
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

// nCk
func combination(k float64, n float64) *big.Float {
	// fmt.Println("Calling comb3, n = ", n, ", k = ", k)
	if k > n {
		t0 := big.NewFloat(0.0)
		return t0
	}
	if k*2 > n {
		k = n - k
	}
	if k == 0 {
		t1 := big.NewFloat(1.0)
		return t1
	}
	result := big.NewFloat(n)
	for i := 2.0; i <= k; i++ {
		result = result.Mul(result, big.NewFloat(n-i+1))
		result = result.Quo(result, big.NewFloat(i))
	}
	return result
}

// n - sample size, p - fraction of malicious nodes in complete set, g - fraction of uncorrupted nodes in sample
func sampling(n float64, p float64, g float64) float64 {
	chance := 0.0
	for k := n * g; k <= n; k++ {
		chance += math.Pow(p, k) * math.Pow(1-p, n-k) * combination3(k, n)
	}
	return chance
}

// base^exp
func exp(base float64, exponent float64) *big.Float {
	// fmt.Println("exp()")
	mul := big.NewFloat(1.0)
	for i := 1.0; i <= exponent; i++ {
		mul = new(big.Float).Mul(mul, big.NewFloat(base))
	}
	return mul
}

// calculate binomial coefficients
func binomial(k int, w int, p float64) *big.Float {
	combWX := combination(float64(k), float64(w))
	pK := exp(p, float64(k))
	qWK := exp(1.0-p, float64(w-k))
	result := new(big.Float).Mul(combWX, pK)
	result = result.Mul(result, qWK)
	return result
}

// sum of binomial coefficients
func binomialsum(j int, w int, p float64) *big.Float {
	sum := big.NewFloat(0.0)
	for k := 0; k <= j; k++ {
		sum = sum.Add(sum, binomial(k, w, p))
	}
	// fmt.Println("Returning binomialsum() ", sum)
	return sum
}

// sortition function as defined in Algorand paper
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
	valuebig := big.NewFloat(value)
	lowerLimit := binomialsum(j, OwnBalance, p)
	upperLimit := binomialsum(j+1, OwnBalance, p)
	for (valuebig.Cmp(lowerLimit) == -1 || valuebig.Cmp(upperLimit) >= 0) && lowerLimit.Cmp(upperLimit) != 0 {
		fmt.Println("Obtained vote for zone [", lowerLimit, ",", upperLimit, ")", "for j = ", j)
		j++
		lowerLimit = big.NewFloat(0.0)
		lowerLimit = binomialsum(j, OwnBalance, p)
		upperLimit = binomialsum(j+1, OwnBalance, p)
		big1 := big.NewFloat(1.0)
		if lowerLimit.Cmp(big1) >= 0 {
			break
		}
	}
	return hash, proof, message, j
}

// verify sortition votes
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
	valuebig := big.NewFloat(value)
	lowerLimit := binomialsum(j, OwnBalance, p)
	upperLimit := binomialsum(j+1, OwnBalance, p)
	for (valuebig.Cmp(lowerLimit) == -1 || valuebig.Cmp(upperLimit) >= 0) && lowerLimit.Cmp(upperLimit) != 0 {
		j++
		lowerLimit = binomialsum(j, OwnBalance, p)
		upperLimit = binomialsum(j+1, OwnBalance, p)
		big1 := big.NewFloat(1.0)
		if lowerLimit.Cmp(big1) >= 0 {
			break
		}
	}

	return j
}

func main() {
	// generate random public and private keys
	pk, sk, _ := GenerateKey(nil)

	bal1 := 50000
	hash, proof, _, count1 := Sortition(sk, 1, 1, bal1)

	resultVerify := VerifySort(pk, hash, proof, 1, 1, bal1)

	if count1 == resultVerify {
		fmt.Println("Verified, Votes = ", count1, "/", bal1)
	}
}
