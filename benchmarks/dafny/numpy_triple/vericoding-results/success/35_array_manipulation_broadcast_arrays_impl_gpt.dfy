// <vc-preamble>
// Method to broadcast two 1D arrays against each other following NumPy broadcasting rules
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Provide max function and a recursive replicate to avoid comprehension parse issues */
function MaxInt(x: int, y: int): int
  ensures MaxInt(x, y) == (if x > y then x else y)
{
  if x > y then x else y
}

/* helper modified by LLM (iteration 2): Implement ReplicateReal using simple recursion (avoids comprehension parse error) */
function ReplicateReal(x: real, n: int): seq<real>
  requires n >= 0
  ensures |ReplicateReal(x, n)| == n
  ensures forall i :: 0 <= i < n ==> ReplicateReal(x, n)[i] == x
  decreases n
{
  if n == 0 then [] else ReplicateReal(x, n - 1) + [x]
}
// </vc-helpers>

// <vc-spec>
method BroadcastArrays(a: seq<real>, b: seq<real>) returns (a_broadcast: seq<real>, b_broadcast: seq<real>)
  // Precondition: broadcasting is valid when one array has size 1 or both have same size
  requires |a| == 1 || |b| == 1 || |a| == |b|
  requires |a| > 0 && |b| > 0
  
  // Postconditions: both output arrays have the same size equal to max of input sizes
  ensures |a_broadcast| == if |a| > |b| then |a| else |b|
  ensures |b_broadcast| == if |a| > |b| then |a| else |b|
  ensures |a_broadcast| == |b_broadcast|
  
  // Broadcasting rules for first array
  ensures |a| == 1 ==> forall i :: 0 <= i < |a_broadcast| ==> a_broadcast[i] == a[0]
  ensures |b| == 1 && |a| > 1 ==> forall i :: 0 <= i < |a_broadcast| && i < |a| ==> a_broadcast[i] == a[i]
  ensures |a| == |b| ==> forall i :: 0 <= i < |a_broadcast| && i < |a| ==> a_broadcast[i] == a[i]
  
  // Broadcasting rules for second array
  ensures |b| == 1 ==> forall i :: 0 <= i < |b_broadcast| ==> b_broadcast[i] == b[0]
  ensures |a| == 1 && |b| > 1 ==> forall i :: 0 <= i < |b_broadcast| && i < |b| ==> b_broadcast[i] == b[i]
  ensures |a| == |b| ==> forall i :: 0 <= i < |b_broadcast| && i < |b| ==> b_broadcast[i] == b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implement broadcasting via replication when needed */
  var n := if |a| > |b| then |a| else |b|;
  if |a| == 1 {
    a_broadcast := ReplicateReal(a[0], n);
  } else {
    a_broadcast := a;
  }
  if |b| == 1 {
    b_broadcast := ReplicateReal(b[0], n);
  } else {
    b_broadcast := b;
  }
}
// </vc-code>
