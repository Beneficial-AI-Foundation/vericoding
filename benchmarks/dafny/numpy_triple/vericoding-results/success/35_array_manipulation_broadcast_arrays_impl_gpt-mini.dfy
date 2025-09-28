// <vc-preamble>
// Method to broadcast two 1D arrays against each other following NumPy broadcasting rules
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): returns maximum of two sequence lengths */
function MaxLen(a: seq<real>, b: seq<real>): nat {
  if |a| > |b| then |a| else |b|
}

/* helper modified by LLM (iteration 2): builds a sequence repeating v n times */
function RepeatVal(v: real, n: nat): seq<real>
  ensures |RepeatVal(v, n)| == n && (forall i :: 0 <= i < n ==> RepeatVal(v, n)[i] == v)
  decreases n
{
  if n == 0 then [] else [v] + RepeatVal(v, n - 1)
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
/* code modified by LLM (iteration 2): implement broadcasting using helpers */
{
  var len: nat := MaxLen(a, b);
  if |a| == 1 {
    a_broadcast := RepeatVal(a[0], len);
  } else {
    a_broadcast := a;
  }
  if |b| == 1 {
    b_broadcast := RepeatVal(b[0], len);
  } else {
    b_broadcast := b;
  }
}
// </vc-code>
