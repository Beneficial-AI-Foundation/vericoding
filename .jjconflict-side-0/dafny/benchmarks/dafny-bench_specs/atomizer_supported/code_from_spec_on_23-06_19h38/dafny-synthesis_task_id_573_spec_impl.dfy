//IMPL UniqueProduct
method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
    var seen: set<int> := {};
    product := 1;
    
    /* code modified by LLM (iteration 4): Fixed loop syntax from 'for i := 0 to arr.Length' to 'var i := 0; while i < arr.Length' */
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant seen == set j | 0 <= j < i :: arr[j]
        invariant product == SetProduct(seen)
    {
        /* code modified by LLM (iteration 4): Fixed logic to only multiply when element is new, but always update seen to maintain invariant */
        if arr[i] !in seen {
            var newSeen := seen + {arr[i]};
            SetProductLemma(newSeen, arr[i]);
            product := product * arr[i];
        }
        // Always update seen to maintain the invariant that seen == set j | 0 <= j < i+1 :: arr[j]
        seen := seen + {arr[i]};
        /* code modified by LLM (iteration 4): Added increment statement for loop variable */
        i := i + 1;
    }
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