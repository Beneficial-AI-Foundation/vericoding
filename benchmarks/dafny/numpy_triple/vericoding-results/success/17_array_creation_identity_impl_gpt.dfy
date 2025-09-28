// <vc-preamble>
// Type alias to represent floating-point numbers
type Float = real

// Method to create an n×n identity matrix
// </vc-preamble>

// <vc-helpers>
function RowUpTo(n: nat, i: nat, k: nat): seq<Float>
  requires i < n
  requires k <= n
  ensures |RowUpTo(n, i, k)| == k
  ensures forall j :: 0 <= j < k ==> RowUpTo(n, i, k)[j] == (if i == j then 1.0 else 0.0)
  decreases k
{
  if k == 0 then []
  else RowUpTo(n, i, k - 1) + [if i == k - 1 then 1.0 else 0.0]
}

function Row(n: nat, i: nat): seq<Float>
  requires i < n
  ensures |Row(n, i)| == n
  ensures forall j :: 0 <= j < n ==> Row(n, i)[j] == (if i == j then 1.0 else 0.0)
{
  RowUpTo(n, i, n)
}

function MatrixUpTo(n: nat, k: nat): seq<seq<Float>>
  requires k <= n
  ensures |MatrixUpTo(n, k)| == k
  ensures forall r :: 0 <= r < k ==> MatrixUpTo(n, k)[r] == Row(n, r)
  decreases k
{
  if k == 0 then []
  else MatrixUpTo(n, k - 1) + [Row(n, k - 1)]
}

function IdentityMatrix(n: nat): seq<seq<Float>>
  ensures |IdentityMatrix(n)| == n
  ensures forall i :: 0 <= i < n ==> |IdentityMatrix(n)[i]| == n
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> IdentityMatrix(n)[i][j] == (if i == j then 1.0 else 0.0)
{
  MatrixUpTo(n, n)
}
// </vc-helpers>

// <vc-spec>
method Identity(n: nat) returns (result: seq<seq<Float>>)
  // Precondition: n is a valid size for a matrix
  requires n >= 0
  
  // Postconditions: result is an n×n identity matrix
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> |result[i]| == n
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> 
    result[i][j] == (if i == j then 1.0 else 0.0)
// </vc-spec>
// <vc-code>
{
  result := IdentityMatrix(n);
}
// </vc-code>
