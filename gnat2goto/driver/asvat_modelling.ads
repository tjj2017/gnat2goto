with Types;             use Types;
package ASVAT_Modelling is
   Model_List : constant String :=
     ("Non_Det#" & "Non_Det_In_Type#");

   function Is_Model (S : String) return Boolean;

   procedure Make_Model (Name : String; Outputs : Elist_Id);

end ASVAT_Modelling;
