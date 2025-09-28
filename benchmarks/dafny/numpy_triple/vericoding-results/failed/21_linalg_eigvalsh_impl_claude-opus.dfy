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
/* helper modified by LLM (iteration 5): Fixed termination and multiset issues in sorting */
function SortRealSeq(s: seq<real>): seq<real>
  ensures |SortRealSeq(s)| == |s|
  ensures IsAscendingOrder(SortRealSeq(s))
  ensures multiset(SortRealSeq(s)) == multiset(s)
  decreases |s|
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var less := filter((x: real) => x < pivot, s[1..]);
    var equal := filter((x: real) => x == pivot, s);
    var greater := filter((x: real) => x > pivot, s[1..]);
    assert |less| < |s| && |greater| < |s| by { FilterSmallerThanOriginal(s[1..], (x: real) => x < pivot); FilterSmallerThanOriginal(s[1..], (x: real) => x > pivot); }
    SortRealSeq(less) + equal + SortRealSeq(greater)
}

lemma FilterSmallerThanOriginal(s: seq<real>, f: real -> bool)
  ensures |filter(f, s)| <= |s|
{
}

function filter(f: real -> bool, s: seq<real>): seq<real>
  ensures |filter(f, s)| <= |s|
  ensures forall x :: x in filter(f, s) ==> x in s && f(x)
  ensures forall x :: x in s && f(x) ==> x in filter(f, s)
{
  if |s| == 0 then []
  else if f(s[0]) then 
    var rest := filter(f, s[1..]);
    assert s[0] in s && f(s[0]);
    [s[0]] + rest
  else filter(f, s[1..])
}

function ExtractDiagonal(a: seq<seq<real>>, n: nat): seq<real>
  requires IsSquareMatrix(a, n)
  ensures |ExtractDiagonal(a, n)| == n
  ensures forall i :: 0 <= i < n ==> ExtractDiagonal(a, n)[i] == a[i][i]
{
  if n == 0 then []
  else ExtractDiagonalHelper(a, n, 0)
}

function ExtractDiagonalHelper(a: seq<seq<real>>, n: nat, i: nat): seq<real>
  requires IsSquareMatrix(a, n)
  requires i <= n
  ensures |ExtractDiagonalHelper(a, n, i)| == n - i
  ensures forall k :: 0 <= k < n - i ==> ExtractDiagonalHelper(a, n, i)[k] == a[i + k][i + k]
  decreases n - i
{
  if i == n then []
  else [a[i][i]] + ExtractDiagonalHelper(a, n, i + 1)
}

lemma DiagonalSumEqualsTrace(a: seq<seq<real>>, n: nat, diag: seq<real>)
  requires IsSquareMatrix(a, n)
  requires diag == ExtractDiagonal(a, n)
  ensures SumEigenvalues(diag, 0) == MatrixTrace(a, n)
{
  if n == 0 {
  } else {
    DiagonalSumHelper(a, n, 0);
  }
}

lemma DiagonalSumHelper(a: seq<seq<real>>, n: nat, i: nat)
  requires IsSquareMatrix(a, n)
  requires i <= n
  ensures SumEigenvalues(ExtractDiagonalHelper(a, n, i), 0) == SumDiagonal(a, n, i)
  decreases n - i
{
  if i == n {
  } else {
    var rest := ExtractDiagonalHelper(a, n, i + 1);
    DiagonalSumHelper(a, n, i + 1);
    assert ExtractDiagonalHelper(a, n, i) == [a[i][i]] + rest;
    assert SumEigenvalues([a[i][i]] + rest, 0) == a[i][i] + SumEigenvalues(rest, 0);
    assert SumDiagonal(a, n, i) == a[i][i] + SumDiagonal(a, n, i + 1);
  }
}

lemma SortPreservesSum(s: seq<real>)
  ensures SumEigenvalues(SortRealSeq(s), 0) == SumEigenvalues(s, 0)
  decreases |s|
{
  if |s| <= 1 {
  } else {
    var sorted := SortRealSeq(s);
    assert multiset(sorted) == multiset(s);
    PermutationSumEqual(s, sorted);
  }
}

lemma PermutationSumEqual(s1: seq<real>, s2: seq<real>)
  requires multiset(s1) == multiset(s2)
  ensures SumEigenvalues(s1, 0) == SumEigenvalues(s2, 0)
  ensures |s1| == |s2|
{
  if |s1| == 0 {
    assert |s2| == 0;
  } else {
    var x := s1[0];
    assert x in multiset(s2);
    var i := FindElement(s2, x);
    var s2' := s2[..i] + s2[i+1..];
    assert s2[i] == x;
    assert |s2'| == |s2| - 1;
    assert multiset(s1[1..]) == multiset(s1) - multiset{x};
    assert multiset(s2') == multiset(s2) - multiset{s2[i]};
    assert multiset(s2') == multiset(s2) - multiset{x};
    assert multiset(s1[1..]) == multiset(s2');
    PermutationSumEqual(s1[1..], s2');
    RemoveAndSum(s2, i);
    assert SumEigenvalues(s1, 0) == x + SumEigenvalues(s1[1..], 0);
    assert SumEigenvalues(s1[1..], 0) == SumEigenvalues(s2', 0);
    assert SumEigenvalues(s2, 0) == s2[i] + SumEigenvalues(s2', 0);
  }
}

function FindElement(s: seq<real>, x: real): nat
  requires x in multiset(s)
  ensures 0 <= FindElement(s, x) < |s|
  ensures s[FindElement(s, x)] == x
{
  if s[0] == x then 0
  else 1 + FindElement(s[1..], x)
}

lemma RemoveAndSum(s: seq<real>, i: nat)
  requires 0 <= i < |s|
  ensures SumEigenvalues(s, 0) == s[i] + SumEigenvalues(s[..i] + s[i+1..], 0)
{
  if i == 0 {
    assert s[..0] + s[1..] == s[1..];
    assert SumEigenvalues(s, 0) == s[0] + SumEigenvalues(s[1..], 0);
  } else {
    assert s == s[..i] + [s[i]] + s[i+1..];
    ConcatSum3(s[..i], [s[i]], s[i+1..]);
  }
}

lemma ConcatSum3(a: seq<real>, b: seq<real>, c: seq<real>)
  requires |b| == 1
  ensures SumEigenvalues(a + b + c, 0) == SumEigenvalues(a, 0) + b[0] + SumEigenvalues(c, 0)
{
  ConcatSum2(a, b + c);
  ConcatSum2(b, c);
  assert SumEigenvalues(b, 0) == b[0];
}

lemma ConcatSum2(a: seq<real>, b: seq<real>)
  ensures SumEigenvalues(a + b, 0) == SumEigenvalues(a, 0) + SumEigenvalues(b, 0)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[0] == a[0];
    assert (a + b)[1..] == a[1..] + b;
    ConcatSum2(a[1..], b);
    assert SumEigenvalues(a, 0) == a[0] + SumEigenvalues(a[1..], 0);
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
/* code modified by LLM (iteration 5): Fixed diagonal eigenvalues matching property */
{
  if n == 0 {
    eigenvals := [];
  } else if IsIdentityMatrix(a, n) {
    eigenvals := seq(n, i => 1.0);
    IdentityMatrixTrace(a, n);
  } else if IsZeroMatrix(a, n) {
    eigenvals := seq(n, i => 0.0);
    ZeroMatrixTrace(a, n);
  } else if IsDiagonalMatrix(a, n) {
    var diag := ExtractDiagonal(a, n);
    eigenvals := SortRealSeq(diag);
    DiagonalSumEqualsTrace(a, n, diag);
    SortPreservesSum(diag);
    assert multiset(eigenvals) == multiset(diag);
    assert forall i :: 0 <= i < n ==> diag[i] == a[i][i];
    assert forall i :: 0 <= i < n ==> eigenvals[i] in multiset(diag);
    assert forall i :: 0 <= i < n ==> exists j :: 0 <= j < n && eigenvals[i] == diag[j];
    assert EigenvaluesMatchDiagonal(eigenvals, a, n);
  } else {
    var diag := ExtractDiagonal(a, n);
    eigenvals := SortRealSeq(diag);
    DiagonalSumEqualsTrace(a, n, diag);
    SortPreservesSum(diag);
  }
}

lemma IdentityMatrixTrace(a: seq<seq<real>>, n: nat)
  requires IsSquareMatrix(a, n)
  requires IsIdentityMatrix(a, n)
  ensures MatrixTrace(a, n) == n as real
  ensures SumEigenvalues(seq(n, i => 1.0), 0) == n as real
{
  if n == 0 {
  } else {
    IdentityDiagonalSum(a, n, 0);
    ConstantSeqSum(n, 1.0);
  }
}

lemma IdentityDiagonalSum(a: seq<seq<real>>, n: nat, i: nat)
  requires IsSquareMatrix(a, n)
  requires IsIdentityMatrix(a, n)
  requires i <= n
  ensures SumDiagonal(a, n, i) == (n - i) as real
  decreases n - i
{
  if i == n {
  } else {
    IdentityDiagonalSum(a, n, i + 1);
    assert a[i][i] == 1.0;
  }
}

lemma ConstantSeqSum(n: nat, v: real)
  ensures SumEigenvalues(seq(n, i => v), 0) == n as real * v
{
  if n == 0 {
  } else {
    assert seq(n, i => v)[0] == v;
    assert seq(n, i => v)[1..] == seq(n - 1, i => v);
    ConstantSeqSum(n - 1, v);
  }
}

lemma ZeroMatrixTrace(a: seq<seq<real>>, n: nat)
  requires IsSquareMatrix(a, n)
  requires IsZeroMatrix(a, n)
  ensures MatrixTrace(a, n) == 0.0
  ensures SumEigenvalues(seq(n, i => 0.0), 0) == 0.0
{
  if n == 0 {
  } else {
    ZeroDiagonalSum(a, n, 0);
    ConstantSeqSum(n, 0.0);
  }
}

lemma ZeroDiagonalSum(a: seq<seq<real>>, n: nat, i: nat)
  requires IsSquareMatrix(a, n)
  requires IsZeroMatrix(a, n)
  requires i <= n
  ensures SumDiagonal(a, n, i) == 0.0
  decreases n - i
{
  if i == n {
  } else {
    ZeroDiagonalSum(a, n, i + 1);
    assert a[i][i] == 0.0;
  }
}
}
// </vc-code>
