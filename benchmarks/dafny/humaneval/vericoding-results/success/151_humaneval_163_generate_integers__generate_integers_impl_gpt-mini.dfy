// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): min helper */
function min(a: int, b: int): int {
  if a < b then a else b
}

/* helper modified by LLM (iteration 3): max helper */
function max(a: int, b: int): int {
  if a < b then b else a
}

// </vc-helpers>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> result[i] in {2, 4, 6, 8}
  ensures forall i :: 0 <= i < |result| - 1 ==> result[i] < result[i + 1]
  ensures forall x :: x in result ==> (x >= a && x <= b) || (x >= b && x <= a)
  ensures forall x :: x in {2, 4, 6, 8} && ((x >= a && x <= b) || (x >= b && x <= a)) ==> x in result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): construct result by conditionally appending known choices in order */
  var low := min(a, b);
  var high := max(a, b);
  result := [];
  if 2 >= low && 2 <= high {
    result := result + [2];
  }
  if 4 >= low && 4 <= high {
    result := result + [4];
  }
  if 6 >= low && 6 <= high {
    result := result + [6];
  }
  if 8 >= low && 8 <= high {
    result := result + [8];
  }
}

// </vc-code>
