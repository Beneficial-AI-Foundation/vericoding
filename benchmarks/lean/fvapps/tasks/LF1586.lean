-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def b91encode (s : String) : String := sorry
def b91decode (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem b91_encode_decode_test_case : 
  b91decode (b91encode "test") = "test" := sorry

theorem b91_encode_decode_hello_world : 
  b91decode (b91encode "Hello World!") = "Hello World!" := sorry

theorem b91_encode_decode_inverse (s : String) :
  b91decode (b91encode s) = s := sorry
-- </vc-theorems>