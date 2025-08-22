//ATOM

// returns sum of array
method sum(s: array<int>) returns (a:int)
requires s.Length > 0
ensures sumcheck(s, s.Length) == a
{
  /* code modified by LLM (iteration 1): Implemented proper sum calculation using loop with invariants */
  a := 0;
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant a == sumcheck(s, i)
  {
    a := a + s[i];
    i := i + 1;
  }
}


//ATOM
// sums from index 0 -> i - 1
function sumcheck(s: array<int>, i: int): int
requires 0 <= i <= s.Length
reads s
{
  if i == 0 then 0
  else s[i - 1] + sumcheck(s, i - 1)
}


//IMPL Main
method Main() {
 /* code modified by LLM (iteration 1): Added array initialization and proper method call with precondition satisfaction */
 var a: array<int> := new int[4];
 a[0] := 1;
 a[1] := 3;
 a[2] := 3;
 a[3] := 2;

 /* code modified by LLM (iteration 1): Added assertion to ensure precondition of sum method is satisfied */
 assert a.Length > 0; // This ensures the precondition of sum() is met
 var s := sum(a);
 print "\nThe sum of all elements in [1,3,3,2] is ";
 print s;
}