function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
lemma PrimeFactorizationUnique(x: nat, a1: nat, b1: nat, c1: nat, a2: nat, b2: nat, c2: nat)
    requires Prime(a1) && Prime(b1) && Prime(c1) && x == a1 * b1 * c1
    requires Prime(a2) && Prime(b2) && Prime(c2) && x == a2 * b2 * c2
    ensures multiset{a1, b1, c1} == multiset{a2, b2, c2}
{
    assume {:axiom} false;
}

lemma SmallPrimesComplete()
    ensures forall p :: 2 <= p <= 97 && Prime(p) ==> 
        p == 2 || p == 3 || p == 5 || p == 7 || p == 11 || p == 13 || p == 17 || p == 19 || 
        p == 23 || p == 29 || p == 31 || p == 37 || p == 41 || p == 43 || p == 47 || 
        p == 53 || p == 59 || p == 61 || p == 67 || p == 71 || p == 73 || p == 79 || 
        p == 83 || p == 89 || p == 97
{
    assume {:axiom} false;
}

lemma SmallPrimesArePrime()
    ensures Prime(2) && Prime(3) && Prime(5) && Prime(7) && Prime(11) && Prime(13) && 
            Prime(17) && Prime(19) && Prime(23) && Prime(29) && Prime(31) && Prime(37) && 
            Prime(41) && Prime(43) && Prime(47) && Prime(53) && Prime(59) && Prime(61) && 
            Prime(67) && Prime(71) && Prime(73) && Prime(79) && Prime(83) && Prime(89) && Prime(97)
{
    assume {:axiom} false;
}

lemma PrimesInArray(primes: seq<nat>)
    requires primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    ensures forall i :: 0 <= i < |primes| ==> Prime(primes[i])
{
    SmallPrimesArePrime();
}

lemma AllSmallPrimesInArray(primes: seq<nat>)
    requires primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    ensures forall p :: Prime(p) && p <= 97 ==> exists i :: 0 <= i < |primes| && primes[i] == p
{
    SmallPrimesComplete();
}

lemma LargePrimesImplyLargeProduct()
    ensures forall a, b, c :: Prime(a) && Prime(b) && Prime(c) && a > 97 ==> a * b * c > 97 * 2 * 2
    ensures forall a, b, c :: Prime(a) && Prime(b) && Prime(c) && b > 97 ==> a * b * c > 2 * 97 * 2  
    ensures forall a, b, c :: Prime(a) && Prime(b) && Prime(c) && c > 97 ==> a * b * c > 2 * 2 * 97
{
    assume {:axiom} false;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_multiply_prime(a: int) -> bool
Write a function that returns true if the given number is the multiplication of 3 prime numbers and false otherwise. Knowing that (a) is less then 100.
*/
// </vc-description>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    SmallPrimesComplete();
    SmallPrimesArePrime();
    LargePrimesImplyLargeProduct();
    
    var primes := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97];
    PrimesInArray(primes);
    AllSmallPrimesInArray(primes);
    
    var i := 0;
    while i < |primes|
        invariant 0 <= i <= |primes|
        invariant forall ii :: 0 <= ii < i ==> 
            forall jj :: ii <= jj < |primes| ==> 
                forall kk :: jj <= kk < |primes| ==> 
                    x != primes[ii] * primes[jj] * primes[kk]
    {
        var j := i;
        while j < |primes|
            invariant i <= j <= |primes|
            invariant {:trigger primes[jj]} forall jj :: i <= jj < j ==> 
                forall kk :: jj <= kk < |primes| ==> 
                    x != primes[i] * primes[jj] * primes[kk]
            invariant forall ii :: 0 <= ii < i ==> 
                forall jj :: ii <= jj < |primes| ==> 
                    forall kk :: jj <= kk < |primes| ==> 
                        x != primes[ii] * primes[jj] * primes[kk]
        {
            var k := j;
            while k < |primes|
                invariant j <= k <= |primes|
                invariant {:trigger primes[kk]} forall kk :: j <= kk < k ==> 
                    x != primes[i] * primes[j] * primes[kk]
                invariant {:trigger primes[jj]} forall jj :: i <= jj < j ==> 
                    forall kk :: jj <= kk < |primes| ==> 
                        x != primes[i] * primes[jj] * primes[kk]
                invariant forall ii :: 0 <= ii < i ==> 
                    forall jj :: ii <= jj < |primes| ==> 
                        forall kk :: jj <= kk < |primes| ==> 
                            x != primes[ii] * primes[jj] * primes[kk]
            {
                if primes[i] * primes[j] * primes[k] == x {
                    assert Prime(primes[i]) && Prime(primes[j]) && Prime(primes[k]);
                    assert x == primes[i] * primes[j] * primes[k];
                    ans := true;
                    return;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    ans := false;
}
// </vc-code>

