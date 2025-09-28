// <vc-preamble>
/* Helper function to recursively count elements less than threshold */
function CountLessThanSpec(numbers: seq<int>, threshold: int): nat
    decreases |numbers|
{
    if |numbers| == 0 then
        0
    else
        var first := numbers[0];
        var rest := numbers[1..];
        if first < threshold then
            1 + CountLessThanSpec(rest, threshold)
        else
            CountLessThanSpec(rest, threshold)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Strengthened inductive proof for concatenation, with explicit sequence and definition reasoning */
lemma CountLessThanSpec_Concat(a: seq<int>, b: seq<int>, t: int)
  ensures CountLessThanSpec(a + b, t) == CountLessThanSpec(a, t) + CountLessThanSpec(b, t)
  decreases |a|
{
  if |a| == 0 {
    // Base case: a is empty
    assert CountLessThanSpec(a, t) == 0;
    assert a == a[0..|a|];
    assert |a| == 0;
    assert a == a[0..0];
    assert a[0..0] == [];
    assert a + b == [] + b;
    assert [] + b == b;
    assert CountLessThanSpec(a + b, t) == CountLessThanSpec(b, t);
    assert CountLessThanSpec(a, t) + CountLessThanSpec(b, t) == 0 + CountLessThanSpec(b, t);
    assert CountLessThanSpec(a + b, t) == CountLessThanSpec(a, t) + CountLessThanSpec(b, t);
  } else {
    var first := a[0];
    var rest := a[1..];

    // Induction hypothesis on rest
    CountLessThanSpec_Concat(rest, b, t);

    // Basic sequence facts for concatenation
    assert |a| > 0;
    assert |a + b| == |a| + |b|;
    assert |a + b| > 0;
    assert (a + b)[0] == first;
    assert (a + b)[1..] == rest + b;

    if first < t {
      assert CountLessThanSpec(a, t) == 1 + CountLessThanSpec(rest, t);
      assert CountLessThanSpec(a + b, t) == 1 + CountLessThanSpec(rest + b, t);
      assert CountLessThanSpec(rest + b, t) == CountLessThanSpec(rest, t) + CountLessThanSpec(b, t);
      assert CountLessThanSpec(a + b, t) == (1 + CountLessThanSpec(rest, t)) + CountLessThanSpec(b, t);
      assert CountLessThanSpec(a + b, t) == CountLessThanSpec(a, t) + CountLessThanSpec(b, t);
    } else {
      assert CountLessThanSpec(a, t) == CountLessThanSpec(rest, t);
      assert CountLessThanSpec(a + b, t) == CountLessThanSpec(rest + b, t);
      assert CountLessThanSpec(rest + b, t) == CountLessThanSpec(rest, t) + CountLessThanSpec(b, t);
      assert CountLessThanSpec(a + b, t) == CountLessThanSpec(a, t) + CountLessThanSpec(b, t);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: array<int>, threshold: int) returns (result: nat)
    ensures result == CountLessThanSpec(numbers[..], threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implement counting with a loop invariant mirroring the spec */
  var i: int := 0;
  result := 0;
  assert numbers[0..] == numbers[..];
  while i < numbers.Length
    invariant 0 <= i <= numbers.Length
    invariant result + CountLessThanSpec(numbers[i..], threshold) == CountLessThanSpec(numbers[..], threshold)
    decreases numbers.Length - i
  {
    if numbers[i] < threshold {
      assert |numbers[i..]| > 0;
      assert CountLessThanSpec(numbers[i..], threshold) == 1 + CountLessThanSpec(numbers[i+1..], threshold);
      result := result + 1;
    } else {
      assert |numbers[i..]| > 0;
      assert CountLessThanSpec(numbers[i..], threshold) == CountLessThanSpec(numbers[i+1..], threshold);
    }
    i := i + 1;
  }
  assert |numbers[numbers.Length..]| == 0;
  assert CountLessThanSpec(numbers[numbers.Length..], threshold) == 0;
  assert result == CountLessThanSpec(numbers[..], threshold);
}
// </vc-code>
