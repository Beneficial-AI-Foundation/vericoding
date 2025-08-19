#!/usr/bin/env python3
import os
import re

def extract_spec_blocks(code):
    """Extract SPEC blocks from original code."""
    pattern = r'//SPEC(?:\s+\[[^\]]+\])?\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_impl_blocks(code):
    """Extract IMPL blocks from generated code."""
    pattern = r'//IMPL(?:[ \t]+[^\n]*)?\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_specification(code_block):
    """Extract the specification part (signature + requires + ensures) from a code block."""
    lines = code_block.split('\n')
    spec_lines = []
    in_body = False
    
    for line in lines:
        stripped = line.strip()
        if stripped == '{':
            in_body = True
            break
        if not in_body:
            spec_lines.append(line)
    
    return '\n'.join(spec_lines).strip()

def extract_body(code_block):
    """Extract the body part from a code block."""
    lines = code_block.split('\n')
    body_lines = []
    in_body = False
    brace_count = 0
    
    for line in lines:
        stripped = line.strip()
        if stripped == '{':
            in_body = True
            brace_count += 1
            body_lines.append(line)
        elif in_body:
            body_lines.append(line)
            if stripped == '{':
                brace_count += 1
            elif stripped == '}':
                brace_count -= 1
                if brace_count == 0:
                    break
    
    return '\n'.join(body_lines).strip()

def get_signature(code_block):
    """Extract method/function/lemma signature from code block."""
    lines = code_block.split('\n')
    for line in lines:
        if any(keyword in line for keyword in ['method ', 'function ', 'lemma ']):
            # Return the line up to the first { or requires/ensures
            signature = line.split('{')[0].split('requires')[0].split('ensures')[0].strip()
            return signature
    return None

def merge_spec_with_body(original_spec, generated_body):
    """Merge original specification with generated body."""
    if not original_spec or not generated_body:
        return None
    
    # Combine spec and body
    return original_spec + '\n' + generated_body

def test_real_merge():
    """Test the merge approach with a real example."""
    print("TESTING REAL MERGE APPROACH")
    print("="*80)
    
    # Example original specification (what would be in the input file)
    original_spec_code = """
//ATOM
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//SPEC
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  // Body should be implemented by LLM
}

//SPEC
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  // Body should be implemented by LLM
}
"""
    
    # Example generated code (what the LLM would return)
    generated_code = """
//ATOM
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//IMPL Add
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  if |s1| == 0 && |s2| == 0 {
    res := "0";
    return;
  }
  
  if |s1| == 0 {
    res := s2;
    return;
  }
  
  if |s2| == 0 {
    res := s1;
    return;
  }
  
  var len1 := |s1|;
  var len2 := |s2|;
  var maxLen := if len1 > len2 then len1 else len2;
  
  var result: seq<char> := [];
  var carry := 0;
  var i := 0;
  
  while i < maxLen || carry > 0
    invariant 0 <= i
    invariant 0 <= carry <= 1
    invariant forall j | 0 <= j < |result| :: result[j] == '0' || result[j] == '1'
    decreases (maxLen + 1) - i + carry
  {
    var bit1 := 0;
    var bit2 := 0;
    
    if i < len1 {
      bit1 := if s1[len1 - 1 - i] == '1' then 1 else 0;
    }
    
    if i < len2 {
      bit2 := if s2[len2 - 1 - i] == '1' then 1 else 0;
    }
    
    var sum := bit1 + bit2 + carry;
    var resultBit := if sum % 2 == 1 then '1' else '0';
    
    result := [resultBit] + result;
    carry := sum / 2;
    
    i := i + 1;
  }
  
  if |result| == 0 {
    res := "0";
  } else {
    res := result;
  }
}

//IMPL Sub
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  if |s2| == 0 {
    res := s1;
    return;
  }
  
  var s2_is_zero := true;
  var j := 0;
  while j < |s2|
    invariant 0 <= j <= |s2|
    invariant s2_is_zero ==> forall k | 0 <= k < j :: s2[k] == '0'
  {
    if s2[j] == '1' {
      s2_is_zero := false;
      break;
    }
    j := j + 1;
  }
  
  if s2_is_zero {
    res := s1;
    return;
  }
  
  var len := if |s1| > |s2| then |s1| else |s2|;
  var padded_s1 := s1;
  var padded_s2 := s2;
  
  while |padded_s1| < len
    invariant ValidBitString(padded_s1)
    invariant |padded_s1| <= len
    invariant ValidBitString(s1) ==> Str2Int(padded_s1) == Str2Int(s1)
    decreases len - |padded_s1|
  {
    padded_s1 := "0" + padded_s1;
  }
  
  while |padded_s2| < len
    invariant ValidBitString(padded_s2)
    invariant |padded_s2| <= len
    invariant ValidBitString(s2) ==> Str2Int(padded_s2) == Str2Int(s2)
    decreases len - |padded_s2|
  {
    padded_s2 := "0" + padded_s2;
  }
  
  var result := "";
  var borrow := 0;
  var i := len;
  
  while i > 0
    invariant 0 <= i <= len
    invariant len == |padded_s1| == |padded_s2|
    invariant ValidBitString(padded_s1) && ValidBitString(padded_s2)
    invariant ValidBitString(result)
    invariant |result| == len - i
    invariant 0 <= borrow <= 1
    decreases i
  {
    i := i - 1;
    var bit1 := if padded_s1[i] == '1' then 1 else 0;
    var bit2 := if padded_s2[i] == '1' then 1 else 0;
    
    var diff := bit1 - bit2 - borrow;
    
    if diff >= 0 {
      var result_bit := if diff == 1 then '1' else '0';
      result := [result_bit] + result;
      borrow := 0;
    } else {
      result := ['1'] + result;
      borrow := 1;
    }
  }
  
  var final_result := result;
  while |final_result| > 1 && final_result[0] == '0'
    invariant ValidBitString(final_result)
    invariant |final_result| >= 1
    decreases |final_result|
  {
    final_result := final_result[1..];
  }
  
  if |final_result| == 0 {
    final_result := "0";
  }
  
  res := final_result;
}
"""
    
    print("ORIGINAL SPECIFICATIONS:")
    print("-" * 40)
    spec_blocks = extract_spec_blocks(original_spec_code)
    for i, spec in enumerate(spec_blocks, 1):
        print(f"SPEC {i}:")
        print(spec.strip())
        print()
    
    print("GENERATED IMPLEMENTATIONS:")
    print("-" * 40)
    impl_blocks = extract_impl_blocks(generated_code)
    for i, impl in enumerate(impl_blocks, 1):
        signature = get_signature(impl)
        print(f"IMPL {i} - {signature}:")
        print(impl.strip())
        print()
    
    print("MERGED RESULTS (Original Spec + Generated Body):")
    print("-" * 40)
    
    # Create a map of signatures to bodies
    body_map = {}
    for block in impl_blocks:
        signature = get_signature(block)
        if signature:
            body = extract_body(block)
            body_map[signature] = body
    
    # Merge original specs with generated bodies
    for i, spec in enumerate(spec_blocks, 1):
        orig_specification = extract_specification(spec)
        orig_signature = get_signature(spec)
        
        print(f"MERGED {i} - {orig_signature}:")
        if orig_signature and orig_signature in body_map:
            merged = merge_spec_with_body(orig_specification, body_map[orig_signature])
            print(merged)
        else:
            print("No matching implementation found")
        print()

if __name__ == "__main__":
    test_real_merge() 