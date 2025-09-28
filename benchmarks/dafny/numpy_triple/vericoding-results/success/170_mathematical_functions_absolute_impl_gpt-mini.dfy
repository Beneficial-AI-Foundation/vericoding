// <vc-preamble>
// Method to calculate absolute value element-wise for a sequence of integers
// </vc-preamble>

// <vc-helpers>
lemma AbsMul(a: int, b: int)
  ensures (if a*b >= 0 then a*b else -(a*b)) == (if a >= 0 then a else -a) * (if b >= 0 then b else -b)
{
  if a >= 0 {
    if b >= 0 {
      assert (if a*b >= 0 then a*b else -(a*b)) == a*b;
      assert (if a >= 0 then a else -a) == a;
      assert (if b >= 0 then b else -b) == b;
    } else {
      assert (if a >= 0 then a else -a) == a;
      assert (if b >= 0 then b else -b) == -b;
      if a * b >= 0 {
        assert a == 0;
        assert a*b == 0;
      }
      assert (if a*b >= 0 then a*b else -(a*b)) == -(a*b);
      assert a * -b == -(a*b);
      assert (if a*b >= 0 then a*b else -(a*b)) == a * -b;
    }
  } else {
    if b >= 0 {
      assert (if a >= 0 then a else -a) == -a;
      assert (if b >= 0 then b else -b) == b;
      if a * b >= 0 {
        assert b == 0;
        assert a*b == 0;
      }
      assert (if a*b >= 0 then a*b else -(a*b)) == -(a*b);
      assert -a * b == -(a*b);
      assert (if a*b >= 0 then a*b else -(a*b)) == -a * b;
    } else {
      assert (if a >= 0 then a else -a) == -a;
      assert (if b >= 0 then b else -b) == -b;
      assert (-a) * (-b) == a * b;
      assert (if a*b >= 0 then a*b else -(a*b)) == a*b;
      assert (-a) * (-b) == a*b;
      assert (if a*b >= 0 then a*b else -(a*b)) == (-a) * (-b);
    }
  }
}

// </vc-helpers>

// <vc-spec>
method Absolute(x: seq<int>) returns (result: seq<int>)
  ensures |result| == |x|
  // Basic definition: |x[i]| = x[i] if x[i] ≥ 0, otherwise -x[i]
  ensures forall i :: 0 <= i < |x| ==> result[i] == (if x[i] >= 0 then x[i] else -x[i])
  // Non-negativity: |x[i]| ≥ 0 for all i
  ensures forall i :: 0 <= i < |result| ==> result[i] >= 0
  // Zero preservation: |x[i]| = 0 if and only if x[i] = 0
  ensures forall i :: 0 <= i < |x| ==> (result[i] == 0 <==> x[i] == 0)
  // Idempotence: ||x[i]|| = |x[i]| (absolute of absolute equals absolute)
  ensures forall i :: 0 <= i < |result| ==> 
    (if result[i] >= 0 then result[i] else -result[i]) == result[i]
  // Multiplicativity: |x[i] * y| = |x[i]| * |y| for any integer y
  ensures forall i, y {:trigger x[i] * y} :: 0 <= i < |x| ==> 
    (if (x[i] * y) >= 0 then (x[i] * y) else -(x[i] * y)) == 
    result[i] * (if y >= 0 then y else -y)
// </vc-spec>
// <vc-code>
{
  var arr := new int[|x|];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall j :: 0 <= j < i ==> arr[j] == (if x[j] >= 0 then x[j] else -x[j])
  {
    arr[i] := if x[i] >= 0 then x[i] else -x[i];
    i := i + 1;
  }
  result := arr[..];
}

// </vc-code>
