//IMPL
method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
    var seen: set<int> := {};
    product := 1;
    
    /* code modified by LLM (iteration 4): fixed loop invariants and logic to properly handle duplicates */
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant seen <= (set j | 0 <= j < arr.Length :: arr[j])
        invariant product == SetProduct(seen)
        invariant forall j :: 0 <= j < i ==> arr[j] in seen
    {
        if arr[i] !in seen {
            /* code modified by LLM (iteration 4): apply lemma before updating to establish the multiplication property */
            SetProductLemma(seen + {arr[i]}, arr[i]);
            seen := seen + {arr[i]};
            product := product * arr[i];
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): final assertion to connect loop result with postcondition */
    assert seen == (set j | 0 <= j < arr.Length :: arr[j]);
}

//ATOM
ghost function SetProduct(s : set<int>) : int
{
    if s == {} then 1
    else var x :| x in s; 
         x * SetProduct(s - {x})
}

//ATOM
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