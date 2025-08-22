//IMPL UniqueProduct
method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
    var seen: set<int> := {};
    product := 1;
    
    /* code modified by LLM (iteration 4): converted to while loop with corrected invariants */
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant seen == set j | 0 <= j < i :: arr[j]
        invariant product == SetProduct(seen)
    {
        if arr[i] !in seen {
            /* code modified by LLM (iteration 4): properly handle set update and product calculation */
            seen := seen + {arr[i]};
            SetProductLemma(seen, arr[i]);
            product := product * arr[i];
        }
        /* code modified by LLM (iteration 4): ensure seen is updated correctly for duplicates */
        else {
            // arr[i] is already in seen, so seen remains the same
            // product also remains the same since SetProduct(seen) doesn't change
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): final assertion to help verification */
    assert seen == set j | 0 <= j < arr.Length :: arr[j];
}

// ATOM 

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

// ATOM 
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
            y * x * SetProduct(s - {x} - {y});
            x * y * SetProduct(s - {x} - {y});
            { SetProductLemma(s - {x}, y); }
            x * SetProduct(s - {x});
         }
      }
   }
}