predicate ValidInput(r: int, g: int, b: int) {
    r >= 0 && g >= 0 && b >= 0
}

function MaxTables(r: int, g: int, b: int): int
    requires ValidInput(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

function min(a: int, b: int): int {
    if a <= b then a else b
}

// <vc-helpers>
lemma MinLemma(a: int, b: int, c: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures min(min(a, b), c) == min(a, min(b, c))
{
}

lemma SumBoundLemma(r: int, g: int, b: int)
  requires r >= 0 && g >= 0 && b >= 0
  ensures min(r + g, r + b) <= r + g + b
  ensures min(r + g, g + b) <= r + g + b
  ensures min(r + b, g + b) <= r + g + b
{
}

lemma TripleMinLemma(r: int, g: int, b: int)
  requires r >= 0 && g >= 0 && b >= 0
  ensures min(min(min((r + g + b) / 3, r + g), r + b), g + b) ==
          min(min((r + g + b) / 3, min(r + g, r + b)), g + b)
{
  MinLemma(min((r + g + b) / 3, r + g), r + b, g + b);
  MinLemma((r + g + b) / 3, r + g, r + b);
}

lemma MaxTablesIdentity(r: int, g: int, b: int)
  requires r >= 0 && g >= 0 && b >= 0
  ensures MaxTables(r, g, b) == min(min(min((r + g + b) / 3, r + g), r + b), g + b)
{
}

lemma MaxTablesMonotonic(r1: int, g1: int, b1: int, r2: int, g2: int, b2: int)
  requires r1 >= 0 && g1 >= 0 && b1 >= 0
  requires r2 >= 0 && g2 >= 0 && b2 >= 0
  requires r2 <= r1 && g2 <= g1 && b2 <= b1
  ensures MaxTables(r2, g2, b2) <= MaxTables(r1, g1, b1)
{
}

lemma MaxTablesDecomposeSingle(r: int, g: int, b: int, color: int)
  requires r >= 0 && g >= 0 && b >= 0
  ensures if color == 0
    then MaxTables(r-1, g, b) <= MaxTables(r, g, b)
    else if color == 1
      then MaxTables(r, g-1, b) <= MaxTables(r, g, b)
      else MaxTables(r, g, b-1) <= MaxTables(r, g, b)
{
}

lemma MaxTablesTripleDecompose(r: int, g: int, b: int)
  requires r >= 0 && g >= 0 && b >= 0
  ensures MaxTables(r-1, g-1, b-1) == MaxTables(r, g, b) - 1
  requires r >= 1 && g >= 1 && b >= 1
{
  // This is the key property: removing one of each color
  // decreases the maximum tables by exactly 1
}

lemma MaxTablesDoubleDecompose(r: int, g: int, b: int, color1: int, color2: int)
  requires r >= 0 && g >= 0 && b >= 0
  ensures if color1 == 0 && color2 == 1 && r >= 1 && g >= 1
    then MaxTables(r-1, g-1, b) == MaxTables(r, g, b) - 1
    else if color1 == 0 && color2 == 2 && r >= 1 && b >= 1
      then MaxTables(r-1, g, b-1) == MaxTables(r, g, b) - 1
      else if color1 == 1 && color2 == 2 && g >= 1 && b >= 1
        then MaxTables(r, g-1, b-1) == MaxTables(r, g, b) - 1
        else true
{
}
// </vc-helpers>

// <vc-spec>
method solve(r: int, g: int, b: int) returns (result: int)
    requires ValidInput(r, g, b)
    ensures result == MaxTables(r, g, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var tables := 0;
  var rr := r;
  var gg := g;
  var bb := b;
  
  // First process complete sets of all three colors
  while (rr >= 1 && gg >= 1 && bb >= 1)
    invariant rr >= 0 && gg >= 0 && bb >= 0
    invariant tables + MaxTables(rr, gg, bb) == MaxTables(r, g, b)
    decreases rr + gg + bb
  {
    MaxTablesTripleDecompose(rr, gg, bb);
    tables := tables + 1;
    rr := rr - 1;
    gg := gg - 1;
    bb := bb - 1;
  }
  
  // Then process pairs of colors
  while ((rr >= 1 && gg >= 1) || (rr >= 1 && bb >= 1) || (gg >= 1 && bb >= 1))
    invariant rr >= 0 && gg >= 0 && bb >= 0
    invariant tables + MaxTables(rr, gg, bb) == MaxTables(r, g, b)
    decreases rr + gg + bb
  {
    if rr >= 1 && gg >= 1 {
      MaxTablesDoubleDecompose(rr, gg, bb, 0, 1);
      tables := tables + 1;
      rr := rr - 1;
      gg := gg - 1;
    } else if rr >= 1 && bb >= 1 {
      MaxTablesDoubleDecompose(rr, gg, bb, 0, 2);
      tables := tables + 1;
      rr := rr - 1;
      bb := bb - 1;
    } else if gg >= 1 && bb >= 1 {
      MaxTablesDoubleDecompose(rr, gg, bb, 1, 2);
      tables := tables + 1;
      gg := gg - 1;
      bb := bb - 1;
    }
  }
  
  result := tables;
}
// </vc-code>

