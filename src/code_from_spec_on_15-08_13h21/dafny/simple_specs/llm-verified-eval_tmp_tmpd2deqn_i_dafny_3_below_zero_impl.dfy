//ATOM
function sum(s: seq<int>, n: nat): int
  requires n <= |s|
{
  if |s| == 0 || n == 0 then
    0
  else
    s[0] + sum(s[1..], n-1)
}

//IMPL 
method below_zero(ops: seq<int>) returns (result: bool)
  ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
  var i := 0;
  while i <= |ops|
    invariant 0 <= i <= |ops| + 1
    invariant forall k: nat :: k < i && k <= |ops| ==> sum(ops, k) >= 0
    /* code modified by LLM (iteration 1): added invariant to establish postcondition when no negative sum found */
    invariant i > |ops| ==> forall k: nat :: k <= |ops| ==> sum(ops, k) >= 0
  {
    if sum(ops, i) < 0 {
      /* code modified by LLM (iteration 1): added assertion to help prove postcondition */
      assert exists n: nat :: n <= |ops| && sum(ops, n) < 0;
      result := true;
      return;
    }
    i := i + 1;
  }
  /* code modified by LLM (iteration 1): added assertion to help prove postcondition when loop completes */
  assert forall k: nat :: k <= |ops| ==> sum(ops, k) >= 0;
  assert !(exists n: nat :: n <= |ops| && sum(ops, n) < 0);
  result := false;
}