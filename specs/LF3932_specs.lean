-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ipv4__parser (ipAddr : String) (mask : String) : String × String := sorry

structure OctetList where
  octets : List Nat
  size_eq : octets.length = 4
  range : ∀ x ∈ octets, 0 ≤ x ∧ x ≤ 255
-- </vc-definitions>

-- <vc-theorems>
theorem ipv4_parser_format (ipAddr : String) (mask : String) :
  let (network, host) := ipv4__parser ipAddr mask
  (network.splitOn ".").length = 4 ∧ 
  (host.splitOn ".").length = 4 := sorry

theorem ipv4_parser_range (ipAddr : String) (mask : String) :
  let (network, host) := ipv4__parser ipAddr mask
  let allOctets := (network.splitOn ".") ++ (host.splitOn ".")
  ∀ octet ∈ allOctets, 
    match octet.toNat? with
    | some n => 0 ≤ n ∧ n ≤ 255
    | none => False := sorry

theorem ipv4_parser_reconstruction 
  (ipOctets : OctetList) (maskOctets : OctetList) :
  let ipAddr := String.join (List.intersperse "." (ipOctets.octets.map toString))
  let mask := String.join (List.intersperse "." (maskOctets.octets.map toString))
  let (network, host) := ipv4__parser ipAddr mask
  let netOctets := (network.splitOn ".").filterMap String.toNat?
  let hostOctets := (host.splitOn ".").filterMap String.toNat?
  ∀ i, i < 4 →
    ((netOctets.get! i) ||| (hostOctets.get! i)) = ipOctets.octets.get! i ∧
    netOctets.get! i = (ipOctets.octets.get! i &&& maskOctets.octets.get! i) ∧
    hostOctets.get! i = (ipOctets.octets.get! i &&& ((255 : Nat) - (maskOctets.octets.get! i))) := sorry
-- </vc-theorems>