// <vc-preamble>
function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added predicates for no_duplicates and sorted */
predicate no_duplicates(s: seq<int>)
  ensures no_duplicates(s) <==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate sorted(s: seq<int>)
  ensures sorted(s) <==> forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
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
  /* code modified by LLM (iteration 5): Fixed syntax for set comprehension in invariant. */
  var seen: set<int> := {};
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall e :: e in result ==> e in x && HasNoEvenDigit(e)
    invariant no_duplicates(result)
    invariant sorted(result)
    invariant seen == set r | r in result :: r
  {
    if HasNoEvenDigit(x[i]) && x[i] !in seen {
      seen := seen + {x[i]};
      var pos := 0;
      while pos < |result| && result[pos] < x[i]
        invariant 0 <= pos <= |result|
        invariant forall k :: 0 <= k < pos ==> result[k] < x[i]
      {
        pos := pos + 1;
      }
      result := result[..pos] + [x[i]] + result[pos..];
    }
    i := i + 1;
  }
}
// </vc-code>
