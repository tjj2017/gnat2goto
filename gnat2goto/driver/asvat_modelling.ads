with Types;             use Types;
package ASVAT_Modelling is
   Model_List : constant String :=
     ("Non_Det#" & "Non_Det_In_Type#");

   type Model_Index is range 0 .. Model_List'Length;

   function Find_Model (S : String) return Model_Index;

   function Is_Model (S : String) return Boolean;

   procedure Make_Model (ASVAT_Model : String; Outputs : Elist_Id)
   with Pre => Is_Model (ASVAT_Model);

end ASVAT_Modelling;
