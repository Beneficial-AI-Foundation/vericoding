// <vc-preamble>
function IntPow(base: int, exp: nat): int
    decreases exp
{
    if exp == 0 then
        1
    else
        base * IntPow(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 2): Added loop invariant helper */
function ArrayLengthMatch(len: nat): bool
{
    true
}

lemma PowerLemma(a: int, exp: nat)
    ensures IntPow(a, exp) == if exp == 0 then 1 else a * IntPow(a, exp - 1)
{
}

// </vc-helpers>

// <vc-spec>
method Power(a: array<int>, b: array<nat>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == IntPow(a[i], b[i])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): Fixed loop invariant bounds and termination */
    result := new int[a.Length];
    var i: int := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == IntPow(a[j], b[j])
    {
        var base_val: int := a[i];
        var exp_val: nat := b[i];
        
        if exp_val == 0 {
            result[i] := 1;
        } else {
            var power: int := 1;
            var count: nat := exp_val;
            
            while count > 0
                invariant 0 <= count <= exp_val
                invariant power == IntPow(base_val, exp_val - count)
                decreases count
            {
                power := power * base_val;
                count := count - 1;
            }
            
            result[i] := power;
        }
        
        i := i + 1;
    }
}
// </vc-code>
