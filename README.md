# Algorand Sortition
Basic implementation of Algorand Sortition in Golang using VRFs.
- sortition.go uses normal integers.
- sortitionbig.go uses golang bigint (https://golang.org/pkg/math/big/).

Due to the calculation of bionomial coefficients in the algorithm to determine the intervals for election, integer overflow is very common. To overcome this, the combination functions are optimized to avoid overflows as much as possible. We provide different implementations for the same. 

Even with these optimizations, the limit is eventually reached. To overcome this, we use the bigint package of Golang. Though this scales to larger values, it is slower.

The code provided is uses VRFs from https://github.com/yahoo/coname/blob/master/vrf/vrf.go and only implements the sortition logic.