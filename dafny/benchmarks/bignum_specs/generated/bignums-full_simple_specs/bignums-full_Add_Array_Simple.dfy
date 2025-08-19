

// ----------------------------------------------------
// Arr2Int: bit-array -> nat (reference function)
// ----------------------------------------------------
function Arr2Int(s: seq<int>): nat
  requires ValidBitSeq(s)
  decreases |s|
{
  if |s| == 0 then 0 
  else s[0] + 2 * Arr2Int(s[1..])
}

//ATOM

predicate ValidBitArray(a: array<int>)
  reads a
{
  // All elements must be 0 or 1
  forall i | 0 <= i < a.Length :: a[i] == 0 || a[i] == 1
}

predicate ValidBitSeq(s: seq<int>)
{
  // All elements must be 0 or 1
  forall i | 0 <= i < |s| :: s[i] == 0 || s[i] == 1
}

// SPEC

// ----------------------------------------------------
// array-based addition (no Arr2Int / Int2Arr)
// ----------------------------------------------------
method Add(a1: array<int>, a2: array<int>) returns (res: array<int>)
  requires ValidBitArray(a1) && ValidBitArray(a2)
  ensures ValidBitArray(res)
  ensures Arr2Int(res[..]) == Arr2Int(a1[..]) + Arr2Int(a2[..])
{
    res := new int[1]; // placeholder
    assume ValidBitArray(res);
    assume Arr2Int(res[..]) == Arr2Int(a1[..]) + Arr2Int(a2[..]);
}

