//IMPL CountNeg
method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
{
  /* code modified by LLM (iteration 3): Implemented proper counting logic with loop invariant to satisfy postcondition */
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

//ATOM
function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{
	if idx == 0 then 0 
	else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}

//IMPL Main
method Main()
{
	/* code modified by LLM (iteration 3): Fixed array initialization syntax and implemented proper counting logic */
	var arr: array<int> := new int[4];
	arr[0] := 0;
	arr[1] := -1;
	arr[2] := -2;
	arr[3] := 4;
	var res := CountNeg(arr);
}