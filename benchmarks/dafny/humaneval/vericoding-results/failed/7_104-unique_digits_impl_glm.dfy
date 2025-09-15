// <vc-preamble>
function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper function for sorting */
function min(a: int, b: int): int {
  if a < b then a else b
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
{/* code modified by LLM (iteration 5): fixed sorting invariants and postconditions */
  var filtered := [];
  var i := 0;
  while i < |x|
  invariant 0 <= i <= |x|
  invariant forall j :: 0 <= j < |filtered| ==> HasNoEvenDigit(filtered[j])
  invariant forall j :: 0 <= j < |filtered| ==> filtered[j] in x[0..i]
  {
    if HasNoEvenDigit(x[i]) {
      filtered := filtered + [x[i]];
    }
    i := i + 1;
  }
  
  var unique := [];
  i := 0;
  while i < |filtered|
  invariant 0 <= i <= |filtered|
  invariant forall j :: 0 <= j < |unique| ==> HasNoEvenDigit(unique[j])
  invariant forall j :: 0 <= j < |unique| ==> unique[j] in filtered[0..i]
  invariant forall j :: 0 <= j < |unique| ==> (forall k :: 0 <= k < j ==> unique[k] != unique[j])
  {
    var j := 0;
    var found := false;
    while j < |unique|
    invariant 0 <= j <= |unique|
    invariant found ==> (exists k :: 0 <= k < j && unique[k] == filtered[i])
    {
      if unique[j] == filtered[i] {
        found := true;
      }
      j := j + 1;
    }
    if !found {
      unique := unique + [filtered[i]];
    }
    i := i + 1;
  }
  
  // Sort the unique elements using selection sort
  var sorted := unique;
  i := 0;
  while i < |sorted|
  invariant 0 <= i <= |sorted|
  invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
  invariant multiset(sorted) == multiset(unique)
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
    invariant i + 1 <= j <= |sorted|
    invariant i <= minIndex < |sorted|
    invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
  
  result := sorted;
}
// </vc-code>
