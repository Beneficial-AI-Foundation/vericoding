//ATOM

method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
{
  cnt := 0;
  assume cnt ==> verifyNeg(a, a.Length);
  return cnt;
}

//ATOM

function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{
	if idx == 0 then 0 
	else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}


// SPEC

method Main()
{
	var arr: array<int> := new int[][0,-1,-2,4];
	var res := CountNeg(arr);
}