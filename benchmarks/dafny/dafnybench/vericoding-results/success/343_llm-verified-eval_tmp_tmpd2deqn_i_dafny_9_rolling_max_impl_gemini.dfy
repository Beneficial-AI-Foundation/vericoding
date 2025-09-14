// <vc-preamble>
function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int
{ 
  if a > b then a else b 
}

lemma RollingMaxProperty(prefix: seq<int>, old_max: int, next_val: int)
  requires prefix != []
  requires isMax(old_max, prefix)
  ensures isMax(max(old_max, next_val), prefix + [next_val])
{
}
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
// </vc-spec>
// <vc-code>
{
  result := [numbers[0]];
  var i := 1;
  while i < |numbers|
    invariant |result| == i && 1 <= i <= |numbers|
    invariant forall j :: 0 <= j < i ==> isMax(result[j], numbers[0..j+1])
  {
    var prev_max := result[i-1];
    var new_max := max(prev_max, numbers[i]);

    assert numbers[0..i] != [];
    assert isMax(prev_max, numbers[0..i]);
    RollingMaxProperty(numbers[0..i], prev_max, numbers[i]);

    result := result + [new_max];
    i := i + 1;
  }
}
// </vc-code>
