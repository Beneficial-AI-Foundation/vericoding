// <vc-preamble>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified approach focusing on proving count_set equals 1 */
lemma OnlyPosHasX(a: seq<int>, pos: int, x: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  ensures forall i :: 0 <= i < |a| && i != pos ==> a[i] != x
{
  forall i | 0 <= i < |a| && i != pos
    ensures a[i] != x
  {
    if i < pos {
      if pos > 0 {
        assert a[i] <= a[pos - 1] < x;
      }
    } else {
      assert i > pos;
      assert a[pos] <= a[i];
      if a[i] == x {
        if pos > 0 {
          assert a[pos - 1] < x == a[i];
          assert a[pos - 1] < a[i];
          assert a[pos - 1] <= a[pos] <= a[i];
          assert false;
        } else {
          var j := pos;
          while j < i
            invariant pos <= j < i
            invariant a[j] == x
          {
            assert a[j] <= a[j + 1];
            j := j + 1;
          }
          assert a[j] == x && j == i;
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)

  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x

  ensures count == count_set(a, x)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): prove only pos has value x so count is 1 */
  OnlyPosHasX(a, pos, x);
  
  var indices := set i | 0 <= i < |a| && a[i] == x;
  assert indices == {pos};
  assert |indices| == 1;
  
  count := 1;
}
// </vc-code>
