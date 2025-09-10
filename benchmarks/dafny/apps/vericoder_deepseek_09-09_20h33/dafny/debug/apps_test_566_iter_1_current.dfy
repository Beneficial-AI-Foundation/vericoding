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
  
  while (rr >= 1 && gg >= 1 && bb >= 1)
    invariant rr >= 0 && gg >= 0 && bb >= 0
    invariant tables + MaxTables(rr, gg, bb) == MaxTables(r, g, b)
  {
    tables := tables + 1;
    rr := rr - 1;
    gg := gg - 1;
    bb := bb - 1;
  }
  
  while (rr >= 1 && gg >= 1)
    invariant rr >= 0 && gg >= 0 && bb >= 0
    invariant tables + MaxTables(rr, gg, bb) == MaxTables(r, g, b)
  {
    tables := tables + 1;
    rr := rr - 1;
    gg := gg - 1;
  }
  
  while (rr >= 1 && bb >= 1)
    invariant rr >= 0 && gg >= 0 && bb >= 0
    invariant tables + MaxTables(rr, gg, bb) == MaxTables(r, g, b)
  {
    tables := tables + 1;
    rr := rr - 1;
    bb := bb - 1;
  }
  
  while (gg >= 1 && bb >= 1)
    invariant rr >= 0 && gg >= 0 && bb >= 0
    invariant tables + MaxTables(rr, gg, bb) == MaxTables(r, g, b)
  {
    tables := tables + 1;
    gg := gg - 1;
    bb := bb - 1;
  }
  
  result := tables;
}
// </vc-code>

