"""
Verify that (p, A, x0) is a Pomerance triple.

Usage:
    python3 vpp.py p A x0

Outputs True/False
"""

import sys

def pp_verify(p, A, x0):
    from math import gcd, isqrt

    if p < 5 or p % 2 == 0:
        return False

    q = isqrt(p)                            # p not prime ==> prime divisor < q
    k = (q + 1 + isqrt(4*q)).bit_length()   # least k such that 2^k > q + 1 + 2*sqrt(q)

    if gcd(A * A - 4, p) != 1:
        return False                        # singular

    X, Z = x0 % p, 1
    Zprev = None

    # precompute C = (A + 2)/4 mod p for doubling formula
    C = ((A + 2) * ((p + 1) // 4 if p % 4 == 3 else (3*p +1) //4)) % p
    for i in range(k):
        Zprev = Z
        U,V = (X+Z)*(X+Z) % p, (X-Z)*(X-Z) % p
        W = U - V
        X,Z = U*V % p, W*(V+C*W) % p

    # if p|Z and (Zprev,p)=1 then (p,A,x0) is valid
    return Z % p == 0 and gcd(Zprev, p) == 1 

def main():
    if len(sys.argv) < 4:
        print(f"Usage: {sys.argv[0]} p A x0", file=sys.stderr)
        sys.exit(1)

    p, A, x0 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    print(pp_verify(p,A,x0))

if __name__ == "__main__":
    main()
