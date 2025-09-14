// <vc-preamble>
function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, helpers for sorting are correct. */
predicate IsSorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method Sort(a: seq<int>) returns (b: seq<int>)
    ensures IsSorted(b)
    ensures multiset(a) == multiset(b)
{
    b := [];
    var i: int := 0;
    while i < |a|
        invariant IsSorted(b)
        invariant multiset(b) == multiset(a[..i])
    {
        var e := a[i];
        var j: int := 0;
        while j < |b| && b[j] < e
            invariant 0 <= j <= |b|
            invariant forall l :: 0 <= l < j ==> b[l] < e
        {
            j := j + 1;
        }
        b := b[..j] + [e] + b[j..];
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method UniqueDigits(x: seq<int>) returns (result: seq<int>)

  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): corrected multiset comprehension syntax in loop invariant. */
  var filtered: seq<int> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall e :: e in filtered ==> HasNoEvenDigit(e)
    invariant multiset(filtered) == multiset(x[j] | 0 <= j < i && HasNoEvenDigit(x[j]))
  {
    if HasNoEvenDigit(x[i]) {
      filtered := filtered + [x[i]];
    }
    i := i + 1;
  }
  result := Sort(filtered);
}
// </vc-code>
