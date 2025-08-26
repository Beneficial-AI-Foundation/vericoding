// <vc-helpers>
lemma SetProductAddLemma(s: set<int>, x: int)
  requires x !in s
  ensures SetProduct(s + {x}) == SetProduct(s) * x
{
  if s == {} {
    assert s + {x} == {x};
    assert SetProduct({x}) == x * SetProduct({});
    assert SetProduct({}) == 1;
    assert SetProduct({x}) == x * 1 == x;
    assert SetProduct(s) * x == 1 * x == x;
  } else {
    var s_new := s + {x};
    assert x in s_new;
    
    // Use the existing SetProductLemma which shows SetProduct(s_new) == SetProduct(s_new - {x}) * x
    SetProductLemma(s_new, x);
    
    calc {
      SetProduct(s_new);
      { SetProductLemma(s_new, x); }
      SetProduct(s_new - {x}) * x;
      { assert s_new - {x} == s; }
      SetProduct(s) * x;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
// </vc-spec>
// <vc-code>
{
  var seen: set<int> := {};
  product := 1;
  
  for i := 0 to arr.Length
    invariant seen == set j | 0 <= j < i :: arr[j]
    invariant product == SetProduct(seen)
  {
    if arr[i] !in seen {
      SetProductAddLemma(seen, arr[i]);
      seen := seen + {arr[i]};
      product := product * arr[i];
    }
  }
}
// </vc-code>

ghost function SetProduct(s : set<int>) : int
{
    if s == {} then 1
    else var x :| x in s; 
         x * SetProduct(s - {x})
}

/* 
 * This is necessary because, when we add one element, we need to make sure
 * that the product of the new set, as a whole, is the same as the product
 * of the old set times the new element.
 */
lemma SetProductLemma(s: set <int>, x: int) 
 requires x in s
 ensures SetProduct(s - {x}) * x == SetProduct(s)
{
   if s != {}
   {
      var y :| y in s && y * SetProduct(s - {y}) == SetProduct(s);
      if y == x {}
      else {
         calc {
            SetProduct(s);
            y * SetProduct(s - {y});
            { SetProductLemma(s - {y}, x); }
            y * x * SetProduct(s - {y} - {x});
            { assert s - {x} - {y} == s - {y} - {x};}
            y * x * SetProduct(s - {x} - {y});
            x * y * SetProduct(s - {x} - {y});
            { SetProductLemma(s - {x}, y); }
            x * SetProduct(s - {x});
         }
      }
   }
}