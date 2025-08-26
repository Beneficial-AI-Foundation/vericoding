#!/usr/bin/env python3

import sys
sys.path.append('.')
from vericoding.processing.yaml_processor import extract_sections

# Test with the actual LLM response
llm_response = '''```dafny:vc-helpers
lemma SortedProperty(a: array<int>, low: int, high: int, x: int)
    requires sorted(a)
    requires 0 <= low <= high < a.Length
    requires a[low] > x
    ensures forall i :: 0 <= i <= low ==> a[i] > x

lemma SortedProperty2(a: array<int>, low: int, high: int, x: int)
    requires sorted(a)
    requires 0 <= low <= high < a.Length
    requires a[high] < x
    ensures forall i :: high <= i < a.Length ==> a[i] < x
```

```dafny:vc-code
{
    if a.Length == 0 {
        return -1;
    }
    
    var low := 0;
    var high := a.Length - 1;
    
    while low <= high
        invariant 0 <= low <= a.Length
        invariant -1 <= high < a.Length
        invariant low > high ==> forall i :: 0 <= i < a.Length ==> a[i] != x
        invariant forall i :: 0 <= i < low ==> a[i] < x
        invariant forall i :: high < i < a.Length ==> a[i] > x
    {
        var mid := (low + high) / 2;
        
        if a[mid] == x {
            return mid;
        } else if a[mid] < x {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    return -1;
}
```'''

helpers, code_section = extract_sections(llm_response)
print('=== EXTRACTED SECTIONS ===')
print(f'Helpers length: {len(helpers)}')
print(f'Code length: {len(code_section)}')
print()
print('Helpers:')
print(helpers)
print()
print('Code:')
print(code_section)
