/-
# Problem Statement
Write a function that takes two string parameters, an IP (v4) address and a subnet mask, and returns two strings: the network block, and the host identifier.

The function does not need to support CIDR notation.

# Description
A single IP address with subnet mask actually specifies several addresses: a network block, and a host identifier, and a broadcast address. These addresses can be calculated using a bitwise AND operation on each bit.

(The broadcast address is not used in this kata.)

## Example
A computer on a simple home network might have the following IP and subnet mask:
```
IP: 192.168.2.1
Subnet: 255.255.255.0
(CIDR Notation: 192.168.2.1 /24)
```
In this example, the network block is: **192.168.2.0**. And the host identifier is: **0.0.0.1**. 

## bitwise AND 
To calculate the network block and host identifier the bits in each octet are ANDed together. When the result of the AND operation is '1', the bit specifies a network address (instead of a host address).

To compare the first octet in our example above, convert both the numbers to binary and perform an AND operation on each bit:
```
11000000 (192 in binary)
11111111 (255 in binary)
--------------------------- (AND each bit)
11000000 (192 in binary)
```
So in the first octet, '**192**' is part of the network address. The host identifier is simply '**0**'.

For more information see the [Subnetwork](http://en.wikipedia.org/wiki/Subnetwork) article on Wikipedia.
-/

-- <vc-helpers>
-- </vc-helpers>

def ipv4__parser (ipAddr : String) (mask : String) : String × String := sorry

structure OctetList where
  octets : List Nat
  size_eq : octets.length = 4
  range : ∀ x ∈ octets, 0 ≤ x ∧ x ≤ 255

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

-- Apps difficulty: introductory
-- Assurance level: guarded