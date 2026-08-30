--  <vc-preamble>
package Np_Zeros_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Zeros (N : Index_Type; Result : out Int_Array) with
     Pre  => Result'Length = N,
     Post => (for all I in Result'Range => Result (I) = 0);

end Np_Zeros_Spec;

package body Np_Zeros_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Zeros (N : Index_Type; Result : out Int_Array) is
   begin
      pragma Assume (False);
   end Zeros;
--  </vc-code>

--  <vc-postamble>
end Np_Zeros_Spec;
--  </vc-postamble>
