// <vc-preamble>
predicate ValidInput(A: int, B: int, C: int)
{
    1 <= A <= 1000000000 && 1 <= B <= 1000000000 && 1 <= C <= 1000000000
}

function TripleSum(A: nat, B: nat, C: nat): nat
{
    (A * (A + 1) * B * (B + 1) * C * (C + 1)) / 8
}

function ModularResult(A: nat, B: nat, C: nat): nat
{
    TripleSum(A, B, C) % 998244353
}
// </vc-preamble>

// <vc-helpers>
function ModularInverse8(): nat
{
    124780544  // modular inverse of 8 mod 998244353
}
// </vc-helpers>

// <vc-spec>
method ComputeTripleSum(A: int, B: int, C: int) returns (result: int)
    requires ValidInput(A, B, C)
    ensures result == ModularResult(A as nat, B as nat, C as nat) as int
    ensures 0 <= result < 998244353
// </vc-spec>
// <vc-code>
{
    var mod := 998244353;
    
    // Calculate A*(A+1)*B*(B+1)*C*(C+1)/8 mod 998244353
    var temp1 := ((A as nat) * ((A + 1) as nat)) % mod;
    var temp2 := ((B as nat) * ((B + 1) as nat)) % mod;
    var temp3 := ((C as nat) * ((C + 1) as nat)) % mod;
    
    var product := (temp1 * temp2) % mod;
    product := (product * temp3) % mod;
    
    // Divide by 8 using modular inverse
    var inv8 := ModularInverse8();
    var ans := (product * inv8) % mod;
    
    result := ans as int;
}
// </vc-code>
