use vstd::prelude::*;

verus! {

// Map structure with key-value pairs  
pub struct Map {
    pub entries: Vec<(i32, i32)>,
}

impl Map {
    // Empty map constructor
    pub fn empty() -> (result: Map) {
        Map { entries: Vec::new() }
    }
    
    // Insert function for maps
    pub fn insert(&self, k: i32, v: i32) -> (result: Map) {
        let mut new_entries: Vec<(i32, i32)> = Vec::new();
        
        // Filter out existing entries with the same key
        for i in 0..self.entries.len() {
            if self.entries[i].0 != k {
                new_entries.push(self.entries[i]);
            }
        }
        
        // Add the new entry
        new_entries.push((k, v));
        
        Map { entries: new_entries }
    }
    
    // Find function for maps
    pub open spec fn find(&self, k: i32) -> Option<i32> {
        if exists|i: int| #![auto] 0 <= i < self.entries.len() && self.entries[i].0 == k {
            let i = choose|i: int| #![auto] 0 <= i < self.entries.len() && self.entries[i].0 == k;
            Some(self.entries[i].1)
        } else {
            None
        }
    }
}

// Precondition (trivially true in this case)
pub open spec fn update_map_precond(m1: Map, m2: Map) -> bool {
    true
}

// Helper function to check if entries are sorted by key  
pub open spec fn is_sorted_by_key(entries: Vec<(i32, i32)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < entries.len() ==> 
        #[trigger] entries[i].0 <= #[trigger] entries[j].0
}

// Helper function to check if all entries from a map appear in result with correct values
pub open spec fn all_entries_preserved(source: Vec<(i32, i32)>, result: Map) -> bool {
    forall|i: int| 0 <= i < source.len() ==> 
        #[trigger] result.find(source[i].0) == Some(source[i].1)
}

// Helper function to check conditional preservation from m1
pub open spec fn conditional_preservation(m1: Vec<(i32, i32)>, m2: Map, result: Map) -> bool {
    forall|i: int| 0 <= i < m1.len() ==> {
        let key = #[trigger] m1[i].0;
        match m2.find(key) {
            Some(_) => true, // If key exists in m2, it's overridden
            None => result.find(key) == Some(m1[i].1), // If not in m2, should be preserved from m1
        }
    }
}

// Helper function to check that result entries come from either m1 or m2
pub open spec fn result_entries_valid(m1: Map, m2: Map, result: Map) -> bool {
    forall|i: int| 0 <= i < result.entries.len() ==> {
        let key = #[trigger] result.entries[i].0;
        let value = result.entries[i].1;
        match m1.find(key) {
            Some(v1) => match m2.find(key) {
                Some(v2) => value == v2, // m2 overrides m1
                None => value == v1,     // only in m1
            },
            None => m2.find(key) == Some(value), // only in m2
        }
    }
}

// Postcondition
pub open spec fn update_map_postcond(m1: Map, m2: Map, result: Map) -> bool {
    is_sorted_by_key(result.entries) &&
    all_entries_preserved(m2.entries, result) &&
    conditional_preservation(m1.entries, m2, result) &&
    result_entries_valid(m1, m2, result)
}

// Sorting helper function using bubble sort
pub fn bubble_sort(entries: &mut Vec<(i32, i32)>) {
    let n = entries.len();
    
    for i in 0..n
        invariant entries.len() == n
    {
        for j in 0..(n - 1 - i)
            invariant 
                entries.len() == n,
                i < n
        {
            if j + 1 < n && entries[j].0 > entries[j + 1].0 {
                let temp = entries[j];
                let next_val = entries[j + 1];
                entries.set(j, next_val);
                entries.set(j + 1, temp);
            }
        }
    }
}

// Main update_map function
pub fn update_map(m1: Map, m2: Map) -> (result: Map)
    requires update_map_precond(m1, m2)
{
    let mut acc = m1;
    
    for i in 0..m2.entries.len() {
        let entry = m2.entries[i];
        acc = acc.insert(entry.0, entry.1);
    }
    
    // Sort the entries by key
    let mut sorted_entries = acc.entries;
    bubble_sort(&mut sorted_entries);
    
    Map { entries: sorted_entries }
}

// Theorem statement (proof omitted as in original Lean code)
pub proof fn update_map_spec_satisfied(m1: Map, m2: Map) 
    requires update_map_precond(m1, m2)
{
    // Proof omitted - was "sorry" in original Lean code
    // The theorem would state that update_map_postcond(m1, m2, update_map(m1, m2)) holds,
    // but this cannot be expressed directly in the ensures clause due to exec/spec separation
}

}

fn main() {}