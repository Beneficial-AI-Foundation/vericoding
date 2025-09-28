// <vc-preamble>
// Type alias to represent floating-point numbers
type Float = real

// Method to create an n×n identity matrix
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): build prefix of a row up to k elements */
function BuildRowPrefix(i: nat, n: nat, k: nat): seq<Float>
  requires k <= n
  ensures |BuildRowPrefix(i,n,k)| == k
  ensures forall t :: 0 <= t < k ==> BuildRowPrefix(i,n,k)[t] == (if i == t then 1.0 else 0.0)
{
  if k == 0 then [] else BuildRowPrefix(i, n, k-1) + [ (if i == k-1 then 1.0 else 0.0) ]
}

/* helper modified by LLM (iteration 5): build a full row of length n with 1.0 at index i */
function BuildRow(i: nat, n: nat): seq<Float>
  requires 0 <= i && i < n
  ensures |BuildRow(i,n)| == n
  ensures forall t :: 0 <= t < n ==> BuildRow(i,n)[t] == (if i == t then 1.0 else 0.0)
{
  BuildRowPrefix(i, n, n)
}

/* helper modified by LLM (iteration 5): build identity sequence of size k with rows of length n */
function IdentitySeqAux(k: nat, n: nat): seq<seq<Float>>
  requires k <= n
  ensures |IdentitySeqAux(k,n)| == k
  ensures forall i :: 0 <= i < k ==> |IdentitySeqAux(k,n)[i]| == n
  ensures forall i, j :: 0 <= i < k && 0 <= j < n ==> IdentitySeqAux(k,n)[i][j] == (if i == j then 1.0 else 0.0)
{
  if k == 0 then [] else IdentitySeqAux(k-1, n) + [ BuildRow(k-1, n) ]
}

/* helper modified by LLM (iteration 5): build identity sequence of size n */
function IdentitySeq(n: nat): seq<seq<Float>>
  requires n >= 0
  ensures |IdentitySeq(n)| == n
  ensures forall i :: 0 <= i < n ==> |IdentitySeq(n)[i]| == n
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> IdentitySeq(n)[i][j] == (if i == j then 1.0 else 0.0)
{
  IdentitySeqAux(n, n)
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
  /* code modified by LLM (iteration 5): build identity matrix using IdentitySeq */
  result := IdentitySeq(n);
}
// </vc-code>
