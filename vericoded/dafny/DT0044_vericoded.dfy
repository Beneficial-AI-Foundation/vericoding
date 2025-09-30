// <vc-preamble>
// Method to broadcast two 1D arrays against each other following NumPy broadcasting rules
// </vc-preamble>

// <vc-helpers>

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
  var size := if |a| > |b| then |a| else |b|;
  
  if |a| == 1 {
    a_broadcast := seq(size, i => a[0]);
  } else {
    a_broadcast := a;
  }
  
  if |b| == 1 {
    b_broadcast := seq(size, i => b[0]);
  } else {
    b_broadcast := b;
  }
}
// </vc-code>
