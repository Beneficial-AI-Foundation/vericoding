// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): utility predicate for membership */
function contains(s: seq<int>, v: int): bool {
  exists i :: 0 <= i < |s| && s[i] == v
}

/* helper modified by LLM (iteration 2): check sorted ascending */
function isSorted(s: seq<int>): bool {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 2): check uniqueness (no duplicates) */
function isUnique(s: seq<int>): bool {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}
// </vc-helpers>

// <vc-spec>
method setdiff1d(ar1: seq<int>, ar2: seq<int>) returns (result: seq<int>)
    // Each element in result is from ar1 and not in ar2
    ensures forall i :: 0 <= i < |result| ==> 
        (exists j :: 0 <= j < |ar1| && result[i] == ar1[j]) &&
        (forall k :: 0 <= k < |ar2| ==> result[i] != ar2[k])
    
    // No duplicates in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    
    // Result is sorted in ascending order
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    
    // All unique values from ar1 not in ar2 are included in result
    ensures forall val {:trigger val in ar1} :: 
        ((exists i :: 0 <= i < |ar1| && ar1[i] == val) && 
         (forall j :: 0 <= j < |ar2| ==> ar2[j] != val)) ==>
        (exists k :: 0 <= k < |result| && result[k] == val)
    
    // Completeness: result contains exactly the values that should be there
    ensures forall val :: 
        (val in result) <==> 
        (val in ar1 && val !in ar2)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed set conversion and invariants to compile */
  ghost var S: set<int> := set ar1 - set ar2;
  ghost var R: set<int> := S;
  result := [];
  while R != {}
    invariant R == S - set result
    invariant forall y :: y in set result ==> (forall x :: x in R ==> y <= x)
    invariant forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    invariant forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    decreases |R|
  {
    var m: int :| m in R && forall y :: y in R ==> m <= y;
    result := result + [m];
    R := R - {m};
  }
}
// </vc-code>
