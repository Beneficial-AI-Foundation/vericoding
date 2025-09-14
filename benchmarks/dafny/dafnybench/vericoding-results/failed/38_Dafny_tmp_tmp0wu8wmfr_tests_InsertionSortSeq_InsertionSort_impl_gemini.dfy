// <vc-preamble>
predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed compilation error in forall quantifier syntax */
function Insert(s: seq<int>, x: int): (r: seq<int>)
    requires IsSorted(s)
    ensures IsSorted(r)
    ensures multiset(r) == multiset(s) + multiset{x}
    ensures forall y :: (forall i | 0 <= i < |s| :: y <= s[i]) && y <= x ==> (forall j | 0 <= j < |r| :: y <= r[j])
{
    if |s| == 0 then [x]
    else if x <= s[0] then [x] + s
    else [s[0]] + Insert(s[1..], x)
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): implementation is correct, relies on fixed helpers */
{
  r := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSorted(r)
    invariant multiset(r) == multiset(s[..i])
  {
    r := Insert(r, s[i]);
    i := i + 1;
  }
}
// </vc-code>
