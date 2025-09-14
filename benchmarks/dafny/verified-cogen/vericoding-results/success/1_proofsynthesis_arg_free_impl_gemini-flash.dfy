// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no changes needed, helper is correctly defined */
function IsOdd(x: int): bool { x % 2 != 0 }
// </vc-helpers>

// <vc-spec>
method ChooseOdd()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): removed return statement from void method */
{
  var r := 0;
  if IsOdd(1) { r := 1; }
  if IsOdd(3) { r := 3; }
  if IsOdd(5) { r := 5; }
}
// </vc-code>
