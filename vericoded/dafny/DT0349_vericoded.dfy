// <vc-preamble>
/*
 * Dafny specification for numpy.prod: Return the product of array elements.
 * 
 * Computes the product of all elements in a sequence. For empty sequences,
 * returns 1.0 as the identity element of multiplication.
 * 
 * Note: This specification models floating-point behavior using real numbers.
 * In practice, this would operate on floating-point values with associated
 * precision and rounding behavior.
 */

// Helper function to compute left-fold product of sequence elements
// Models floating-point product computation with left-associative fold
function SeqProductLeftAux(s: seq<real>, acc: real, index: nat): real
    requires index <= |s|
    decreases |s| - index
{
    if index == |s| then acc
    else SeqProductLeftAux(s, acc * s[index], index + 1)
}

// Helper function to compute product of sequence elements
// Models floating-point product computation using left-fold semantics
function SeqProduct(s: seq<real>): real
{
    SeqProductLeftAux(s, 1.0, 0)
}

// Helper predicate to check if any element in sequence is zero
predicate ContainsZero(s: seq<real>)
{
    exists i :: 0 <= i < |s| && s[i] == 0.0
}

// Main product computation method
// Models numpy.prod behavior with floating-point semantics
// </vc-preamble>

// <vc-helpers>
lemma SeqProductLeftAux_acc_zero(s: seq<real>, i: nat)
    requires i <= |s|
    ensures SeqProductLeftAux(s, 0.0, i) == 0.0
    decreases |s| - i
{
  if i == |s| {
  } else {
    SeqProductLeftAux_acc_zero(s, i + 1);
  }
}

lemma SeqProductLeftAux_zero(s: seq<real>, acc: real, i: nat)
    requires i <= |s|
    requires exists k :: i <= k < |s| && s[k] == 0.0
    ensures SeqProductLeftAux(s, acc, i) == 0.0
    decreases |s| - i
{
  var k :| i <= k < |s| && s[k] == 0.0;
  if i == |s| {
  } else if s[i] == 0.0 {
    SeqProductLeftAux_acc_zero(s, i + 1);
  } else {
    assert k != i;
    assert i + 1 <= k < |s|;
    SeqProductLeftAux_zero(s, acc * s[i], i + 1);
  }
}

lemma SeqProductLeftAux_preserve_nonzero(s: seq<real>, acc: real, i: nat)
    requires i <= |s|
    requires acc != 0.0
    requires forall j :: i <= j < |s| ==> s[j] != 0.0
    ensures SeqProductLeftAux(s, acc, i) != 0.0
    decreases |s| - i
{
  if i == |s| {
  } else {
    assert s[i] != 0.0;
    assert acc * s[i] != 0.0;
    SeqProductLeftAux_preserve_nonzero(s, acc * s[i], i + 1);
  }
}

lemma SeqProduct_contains_zero(s: seq<real>)
    requires ContainsZero(s)
    ensures SeqProduct(s) == 0.0
{
  SeqProductLeftAux_zero(s, 1.0, 0);
}

lemma SeqProduct_nonzero_if_no_zero(s: seq<real>)
    requires |s| > 0 && !ContainsZero(s)
    ensures SeqProduct(s) != 0.0
{
  SeqProductLeftAux_preserve_nonzero(s, 1.0, 0);
}
// </vc-helpers>

// <vc-spec>
method Prod(a: seq<real>) returns (result: real)
    ensures result == SeqProduct(a)
    ensures |a| == 0 ==> result == 1.0
    ensures ContainsZero(a) ==> result == 0.0
    ensures |a| > 0 && !ContainsZero(a) ==> result != 0.0
// </vc-spec>
// <vc-code>
{
  result := SeqProduct(a);
  if ContainsZero(a) {
    SeqProduct_contains_zero(a);
  }
  if |a| > 0 && !ContainsZero(a) {
    SeqProduct_nonzero_if_no_zero(a);
  }
}

// </vc-code>
