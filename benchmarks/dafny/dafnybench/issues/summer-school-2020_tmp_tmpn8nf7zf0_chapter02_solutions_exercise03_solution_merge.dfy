// <vc-preamble>
predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}

//lemma SequenceConcat(s:seq<int>, pivot:int)
//  requires 0<=pivot<|s|
//  ensures s[..pivot] + s[pivot..] == s
//{
//}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
//  ensures IsSorted(output)
  ensures SortSpec(a+b, output)
  //decreases |a|+|b|
// </vc-spec>
// <vc-code>
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    invariant 0 <= ai <= |a|
    invariant 0 <= bi <= |b|
    invariant 0 < |output| && ai < |a| ==> output[|output|-1] <= a[ai]
    invariant 0 < |output| && bi < |b| ==> output[|output|-1] <= b[bi]
    invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
    decreases |a|-ai + |b|-bi
  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
      assert b[bo..bi] == [b[bo]];  // discovered by calc
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
      assert a[ao..ai] == [a[ao]];  // discovered by calc
    }
    assert a[..ai] == a[..ao] + a[ao..ai];  // discovered by calc
    assert b[..bi] == b[..bo] + b[bo..bi];  // discovered by calc
//    calc {
//      multiset(a[..ai]) + multiset(b[..bi]);
//      multiset(a[..ao] + a[ao..ai]) + multiset(b[..bo] + b[bo..bi]);
//      multiset(a[..ao]) + multiset(a[ao..ai]) + multiset(b[..bo]) + multiset(b[bo..bi]);
//      multiset(a[..ao]) + multiset(b[..bo]) + multiset(a[ao..ai]) + multiset(b[bo..bi]);
//      multiset(outputo) + multiset(a[ao..ai]) + multiset(b[bo..bi]);
//      multiset(output);
//    }
  }
  assert a == a[..ai];  // derived by calc
  assert b == b[..bi];
//  calc {
//    multiset(output);
//    multiset(a[..ai]) + multiset(b[..bi]);
//    multiset(a) + multiset(b);
//    multiset(a + b);
//  }
}
// </vc-code>
