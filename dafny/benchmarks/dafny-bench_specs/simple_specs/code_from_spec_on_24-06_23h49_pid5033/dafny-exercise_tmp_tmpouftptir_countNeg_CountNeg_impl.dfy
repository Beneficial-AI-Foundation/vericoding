//ATOM
function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{
	if idx == 0 then 0 
	else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}

//IMPL CountNeg
method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
{
    cnt := 0;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant cnt == verifyNeg(a, i)
    {
        if a[i] < 0 {
            cnt := cnt + 1;
        }
        i := i + 1;
    }
}