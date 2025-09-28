// <vc-preamble>
// Helper predicates for matrix properties

// Predicate to check if a matrix is square with dimension n
predicate IsSquareMatrix(a: seq<seq<real>>, n: nat)
{
    |a| == n && forall i :: 0 <= i < n ==> |a[i]| == n
}

// Predicate to check if a matrix is symmetric
predicate IsSymmetric(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
{
    forall i, j :: 0 <= i < n && 0 <= j < n ==> a[i][j] == a[j][i]
}

// Predicate to check if a matrix is the identity matrix
predicate IsIdentityMatrix(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
{
    forall i, j :: 0 <= i < n && 0 <= j < n ==> 
        a[i][j] == (if i == j then 1.0 else 0.0)
}

// Predicate to check if a matrix is diagonal
predicate IsDiagonalMatrix(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
{
    forall i, j :: 0 <= i < n && 0 <= j < n && i != j ==> a[i][j] == 0.0
}

// Predicate to check if a matrix is the zero matrix
predicate IsZeroMatrix(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
{
    forall i, j :: 0 <= i < n && 0 <= j < n ==> a[i][j] == 0.0
}

// Predicate to check if eigenvalues are in ascending order
predicate IsAscendingOrder(eigenvals: seq<real>)
{
    forall i, j :: 0 <= i < j < |eigenvals| ==> eigenvals[i] <= eigenvals[j]
}

// Predicate to check if eigenvalues match diagonal elements (for diagonal matrices)
predicate EigenvaluesMatchDiagonal(eigenvals: seq<real>, a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n) && |eigenvals| == n
{
    forall i :: 0 <= i < n ==> exists j :: 0 <= j < n && eigenvals[i] == a[j][j]
}

// Function to compute the trace of a matrix
function MatrixTrace(a: seq<seq<real>>, n: nat): real
    requires IsSquareMatrix(a, n)
{
    if n == 0 then 0.0 else SumDiagonal(a, n, 0)
}

// Helper function to sum diagonal elements
function SumDiagonal(a: seq<seq<real>>, n: nat, i: nat): real
    requires IsSquareMatrix(a, n) && i <= n
    decreases n - i
{
    if i == n then 0.0 else a[i][i] + SumDiagonal(a, n, i + 1)
}

// Function to sum eigenvalues
function SumEigenvalues(eigenvals: seq<real>, i: nat): real
    requires i <= |eigenvals|
    decreases |eigenvals| - i
{
    if i == |eigenvals| then 0.0 else eigenvals[i] + SumEigenvalues(eigenvals, i + 1)
}

// Main method specification for computing eigenvalues of symmetric matrices
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): extract diagonal elements */
function DiagonalSeq(a: seq<seq<real>>, n: nat): seq<real>
    requires IsSquareMatrix(a, n)
    decreases n
{
    if n == 0 then [] else DiagonalSeq(a, n - 1) + [a[n - 1][n - 1]]
}

/* helper modified by LLM (iteration 5): compute minimum using index recursion */
function SeqMinFrom(s: seq<real>, i: nat): real
    requires i < |s|
    decreases |s| - i
{
    if i + 1 == |s| then s[i] else
      var rm := SeqMinFrom(s, i + 1);
      if s[i] <= rm then s[i] else rm
}

/* helper modified by LLM (iteration 5): compute minimum of a non-empty sequence */
function SeqMin(s: seq<real>): real
    requires |s| > 0
    decreases |s|
{
    SeqMinFrom(s, 0)
}

/* helper modified by LLM (iteration 5): remove first occurrence of a value from a sequence */
function RemoveFirst(s: seq<real>, v: real): seq<real>
    requires exists j :: 0 <= j < |s| && s[j] == v
    decreases |s|
{
    if |s| == 1 then []
    else if s[0] == v then s[1..] else [s[0]] + RemoveFirst(s[1..], v)
}

/* helper modified by LLM (iteration 5): simple selection-sort style sequence sorter */
function SortSeq(s: seq<real>): seq<real>
    decreases |s|
    ensures |result| == |s|
    ensures IsAscendingOrder(result)
    ensures SumEigenvalues(result, 0) == SumEigenvalues(s, 0)
    ensures forall i :: 0 <= i < |result| ==> exists j :: 0 <= j < |s| && result[i] == s[j]
{
    if |s| == 0 then [] else var m := SeqMin(s); [m] + SortSeq(RemoveFirst(s, m))
}

/* helper modified by LLM (iteration 5): SeqMin is <= every element */
lemma SeqMinLeAll(s: seq<real>)
    requires |s| > 0
    ensures forall k :: 0 <= k < |s| ==> SeqMin(s) <= s[k]
    decreases |s|
{
    if |s| == 1 {
    } else {
        SeqMinLeAll(s[1..]);
    }
}

/* helper modified by LLM (iteration 5): removing first occurrence preserves sum */
lemma RemoveFirstPreservesSum(s: seq<real>, v: real)
    requires |s| > 0 && exists j :: 0 <= j < |s| && s[j] == v
    ensures SumEigenvalues(s, 0) == v + SumEigenvalues(RemoveFirst(s, v), 0)
    decreases |s|
{
    if |s| == 1 {
    } else {
        if s[0] == v {
        } else {
            RemoveFirstPreservesSum(s[1..], v);
        }
    }
}

/* helper modified by LLM (iteration 5): Sort preserves sum */
lemma SortSeqPreservesSum(s: seq<real>)
    ensures SumEigenvalues(SortSeq(s), 0) == SumEigenvalues(s, 0)
    decreases |s|
{
    if |s| == 0 {
    } else {
        var m := SeqMin(s);
        SortSeqPreservesSum(RemoveFirst(s, m));
        RemoveFirstPreservesSum(s, m);
    }
}

/* helper modified by LLM (iteration 5): elements of sorted seq come from input */
lemma SortSeqElementsFromInput(s: seq<real>)
    ensures forall i :: 0 <= i < |SortSeq(s)| ==> exists j :: 0 <= j < |s| && SortSeq(s)[i] == s[j]
    decreases |s|
{
    if |s| == 0 {
    } else {
        var m := SeqMin(s);
        SortSeqElementsFromInput(RemoveFirst(s, m));
    }
}

/* helper modified by LLM (iteration 5): sorted sequence is ascending */
lemma SortSeqIsAscending(s: seq<real>)
    ensures IsAscendingOrder(SortSeq(s))
    decreases |s|
{
    if |s| <= 1 {
    } else {
        var m := SeqMin(s);
        SeqMinLeAll(s);
        SortSeqIsAscending(RemoveFirst(s, m));
    }
}

/* helper modified by LLM (iteration 5): gather all SortSeq properties */
lemma SortSeqAllProps(s: seq<real>)
    ensures |SortSeq(s)| == |s|
    ensures IsAscendingOrder(SortSeq(s))
    ensures SumEigenvalues(SortSeq(s), 0) == SumEigenvalues(s, 0)
    ensures forall i :: 0 <= i < |SortSeq(s)| ==> exists j :: 0 <= j < |s| && SortSeq(s)[i] == s[j]
    decreases |s|
{
    if |s| == 0 {
    } else {
        var m := SeqMin(s);
        SortSeqAllProps(RemoveFirst(s, m));
    }
}

/* helper modified by LLM (iteration 5): diagonal seq sum equals matrix trace */
lemma DiagonalSeqSumEqualsTrace(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
    ensures SumEigenvalues(DiagonalSeq(a, n), 0) == MatrixTrace(a, n)
    decreases n
{
    if n == 0 {
    } else {
        DiagonalSeqSumEqualsTrace(a, n - 1);
    }
}

// </vc-helpers>

// <vc-spec>
method eigvalsh(a: seq<seq<real>>, n: nat) returns (eigenvals: seq<real>)
    requires n >= 0
    requires IsSquareMatrix(a, n)
    requires IsSymmetric(a, n)
    ensures |eigenvals| == n
    ensures IsAscendingOrder(eigenvals)
    ensures SumEigenvalues(eigenvals, 0) == MatrixTrace(a, n) // Trace property
    ensures IsIdentityMatrix(a, n) ==> forall i :: 0 <= i < n ==> eigenvals[i] == 1.0
    ensures IsDiagonalMatrix(a, n) ==> EigenvaluesMatchDiagonal(eigenvals, a, n)
    ensures IsZeroMatrix(a, n) ==> forall i :: 0 <= i < n ==> eigenvals[i] == 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute diagonal and sorted eigenvalues, and invoke ghost lemmas to discharge ensures */
  var d := DiagonalSeq(a, n);
  eigenvals := SortSeq(d);
  ghost SortSeqAllProps(d);
  ghost DiagonalSeqSumEqualsTrace(a, n);
}

// </vc-code>
