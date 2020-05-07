with Opt;
with Stand;
with Snames;                  use Snames;
with Atree;                   use Atree;
with Sinfo;                   use Sinfo;
with Einfo;                   use Einfo;
with Sem_Util;                use Sem_Util;
with Sem_Aux;                 use Sem_Aux;
with Tree_Walk;               use Tree_Walk;
with GOTO_Utils;              use GOTO_Utils;

with Treepr;                  use Treepr;
with Text_IO;                 use Text_IO;

package body ASVAT.Size_Model is

   -----------------------
   -- Do_Attribute_Size --
   -----------------------

   function Do_Attribute_Size (N : Node_Id) return Irep
   is
      --  S'Size where S is a scalar subtype is nearly always
      --  known at compile time, and the front-end substitues a listeral
      --  into the AST replacing the call to attribute size (and Value_Size).
      --  In such cases, obviously, this function is not called.
      --
      --  As documented in the front-end package declaration, Einfo, the
      --  the value retuned by attribute Size are "peculiar" and they are
      --  further complicated by the pragma Use_VADS_Size which causes the
      --  front-end to take the VADS size attribute iterpretation.
      --  The pragma Use_VADS_Size is applied as part of the Rational profile.
      --
      --  The Ada RM states:
      --  S'Size for every subtype S:
      --    If S is definite, denotes the size (in bits) that the
      --    implementation would choose for the following objects of subtype S:
      --      A record component of subtype S when the record type is packed.
      --      The formal parameter of an instance of Unchecked_Conversion
      --         that converts from subtype S to some other subtype.
      --    If S is indefinite, the meaning is implementation defined.
      --  For a prefix X that denotes an object:
      --    Denotes the size in bits of the representation of the object.
      --
      --  The `'VADS_Size' attribute is intended to make it easier to port
      --  legacy code which relies on the semantics of `'Size' as implemented
      --  by the VADS Ada 83 compiler.  GNAT makes a best effort at
      --  duplicating the same semantic interpretation.
      --  In particular, `'VADS_Size' applied to a predefined or other
      --  primitive type with no Size clause yields the Object_Size
      --  (for example, `Natural'Size' is 32 rather than 31 on
      --  typical machines) [ASVAT-TJJ this is done by the front-end].
      --  In addition `'VADS_Size' applied to an object gives the result that
      --  would be obtained by applying it to the corresponding type.
      --
      --  From Einfo:
      --    The function RM_Size should be used to obtain the value of S'Size.
      --    [ASVAT TJJ: RM_Size has the value 0 if size of the subtype is not
      --     known to the front-end].
      --    The function Esize should be used to obtain the value of X'Size.
      --
      --  Esize can be applied to a subtype in which case it gives the default
      --  size of an object of that type, or an object.
      --  Often, it returns 0 if the size of the type or object is not known
      --  by the front-end.
      --
      --  The size of a definite subtype can be specified using a
      --  size representaion clause and then the front-end knows this value.
      --  Etype (and RM_Type) return 0 even if a size representation clause
      --  is applied to an indefinite type.  The front-end seems to ignore
      --  such a representation clause and it does not appear in the AST.
      --  A constrained (definite) subtype of an indefinite subtype van have
      --  a Value_Size attribute applied and than the front-end knows this
      --  value.
      --
      --  There are still other occasions when the front end returns 0 for one
      --  or other or both RM_Size and Esize, so Do_Attribute_Size tries to
      --  return a sensible value.

      Constant_Type : constant Irep :=
        Do_Type_Reference (Stand.Universal_Integer);
      The_Prefix    : constant Node_Id := Prefix (N);
      Prefix_Etype  : constant Entity_Id := Etype (The_Prefix);

      Use_VADS_Size : constant Boolean :=
        Opt.Use_VADS_Size or else
        Get_Attribute_Id (Attribute_Name (N)) = Attribute_VADS_Size;

      --  The result size.
      The_Size      : Uint;

   begin
      --  In such cases gnat2goto uses the default size of the
      --  object obtained by applying Esize to its subtype.
      --  Unfortunately, this may also return 0 if the size of
      --  the subtype is not known by the frontend.
      Put_Line ("Attribute size");
      Put_Line ("Implicit_Packing = " &
                  Boolean'Image (Opt.Implicit_Packing));
      Put_Line ("Use_VADS_Size = " &
                  Boolean'Image (Opt.Use_VADS_Size));
      if ASVAT.Size_Model.Has_Size_Rep_Clause (Prefix_Etype)
      then
         Put_Line ("Has size rep clause = " &
                     Int'Image
                     (UI_To_Int
                        (ASVAT.Size_Model.Get_Rep_Size
                             (Prefix_Etype))));
      end if;

      Print_Node_Briefly (The_Prefix);
      Print_Node_Briefly (Prefix_Etype);
      Put_Line ("Has_Size_Clause Prefix Etype " &
                  Boolean'Image
                  (Has_Size_Clause (Prefix_Etype)));
      Put_Line ("Has_Size_Clause Etype Prefix Etype " &
                  Boolean'Image
                  (Has_Size_Clause (Etype (Prefix_Etype))));

      Put_Line (Boolean'Image
                (Is_Definite_Subtype (Prefix_Etype)));
      if not Is_Definite_Subtype (Prefix_Etype) then
         Report_Unhandled_Node_Empty
           (The_Prefix,
            "Do_Expression",
            "Size attribute applied to indefinite " &
              "type is implementation defined");
         Put_Line ("The size " &
                     Int'Image
                     (UI_To_Int (RM_Size (Prefix_Etype))));
         Put_Line ("The Esize " &
                     Int'Image
                     (UI_To_Int (Esize (Prefix_Etype))));
         --  The size returned by the fron-end is almost certainly 0
         --  when applied to an indefinite type, and there is not really
         --  anything gnat2goto cand do.
         --  Ada RM states that the result is implementation dependent
         --  but tha back-end does put out a sensible value, which of course,
         --  gnat2goto has  no access to.
         --  Reporting an unhandled node is the best it can do.
         The_Size := RM_Size (Prefix_Etype);

      elsif Use_VADS_Size then
         --  If this attribute is used or
         --  the option is set by prgma Use_VADS_Size, which is part of
         --  pragma Profile (Rational), for  an object, X, X'Size
         --  is equivalent to Value_Size (except for primitive and basic
         --  types which are handled by the front end). Therfore,
         --  RM_Size can be used for both S'Size and X'Size.
         Put_Line ("VADS size = " &
                     Int'Image
                     (UI_To_Int (RM_Size (Prefix_Etype))));
         Put_Line ("Esize = " &
                     Int'Image
                     (UI_To_Int (Esize (Prefix_Etype))));
         if Nkind (The_Prefix) = N_Slice then
            --  When 'Size is applied to a slice, Esize returns 0 and
            --  RM_Size returns the size of the type of the components
            --  times the number of components in the slice.
            --  It does not take account of any packing.  The back-end does,
            --  however , so there could be discrepencies.
            --  Gnat2goto issues a warning report.
            Report_Unhandled_Node_Empty
              (The_Prefix,
               "Do_Attribute_Size",
               "A Size atribute applied to a slice " &
                 "may give an inaccurate value");
            Print_Node_Briefly (Prefix (The_Prefix));
            Print_Node_Briefly (Etype (Prefix (The_Prefix)));
            Put_Line ("Size = " &
                        Int'Image (UI_To_Int
                        (Component_Size
                             (Etype (Prefix (The_Prefix))))));
         end if;

         The_Size := RM_Size (Prefix_Etype);

         if UI_To_Int (The_Size) = 0 then
            if Is_Base_Type (Prefix_Etype) then
               Report_Unhandled_Node_Empty
                 (The_Prefix,
                  "Do_Expression",
                  "The size of the composite is not known " &
                    "by the front-end. " &
                    "Use a size represntation clause");
            else
               if ASVAT.Size_Model.Has_Size_Rep_Clause
                 (Implementation_Base_Type (Prefix_Etype))
               then
                  Put_Line
                    ("Base type of subtype has size rep " &
                       Int'Image
                       (UI_To_Int
                            (ASVAT.Size_Model.Get_Rep_Size
                                 (Implementation_Base_Type
                                    (Prefix_Etype)))));
               end if;

               The_Size := RM_Size
                 (Implementation_Base_Type
                    (Prefix_Etype));
               if The_Size = Uint_0 then
                  if Is_Definite_Subtype
                    (Implementation_Base_Type (Prefix_Etype))
                  then
                     Report_Unhandled_Node_Empty
                       (The_Prefix,
                        "Do_Expression",
                        "The size of the subtype is not known "
                        &
                          "by the front-end. " &
                          "Apply a size representation " &
                          "to its base type.");
                  else
                     Report_Unhandled_Node_Empty
                       (The_Prefix,
                        "Do_Expression",
                        "The base type of the prefix " &
                          "is indefinite and the result of " &
                          "S'Size " &
                          "is implementation defined.");
                  end if;
               end if;
            end if;
         end if;

      else
         Put_Line ("Attribute_Size");
         Put_Line ("Has pragma Implicit_Packing = " &
                     Boolean'Image (Opt.Implicit_Packing));
         Put_Line ("Has pragma Use_VADS_Size = " &
                     Boolean'Image (Opt.Use_VADS_Size));
         Print_Node_Briefly (The_Prefix);

         if Nkind (The_Prefix) in
           N_Has_Entity | N_Selected_Component
         then
            Put_Line ("Has Entity");
            declare
               The_Entity : constant Entity_Id :=
                 (if Nkind (The_Prefix) =
                      N_Selected_Component
                  then
                     Entity (Selector_Name (The_Prefix))
                  else
                     Entity (The_Prefix));
            begin
               if Is_Object (The_Entity) then
                  declare
                     Object_Size : constant Uint :=
                       Esize (The_Entity);
                     Default_Obj_Size : constant Uint :=
                       Esize (Etype (The_Entity));
                     The_Size_To_Use : constant Uint :=
                       (if UI_To_Int (Object_Size) /= 0
                        then
                           Object_Size
                        elsif UI_To_Int
                          (Default_Obj_Size) /= 0
                        then
                           Default_Obj_Size
                        else
                           UI_Mul
                          (UI_Add
                               (UI_Div
                                    (UI_Sub
                                       (RM_Size
                                          (Etype
                                               (The_Entity)),
                                        1),
                                     8),
                                1),
                           8)
                       );
                  begin
                     Put_Line ("Object_Size = " &
                                 Int'Image
                                 (UI_To_Int (Object_Size)));
                     Put_Line ("Default_Size = " &
                                 Int'Image
                                 (UI_To_Int
                                    (Default_Obj_Size)));
                     Put_Line ("The_Size_To_Use = " &
                                 Int'Image
                                 (UI_To_Int
                                    (The_Size_To_Use)));
                     The_Size := The_Size_To_Use;
                  end;

               elsif Is_Type (The_Entity) then
                  Put_Line ("Is type");
                  --  Since the attribute is applied to
                  --  a subtype,
                  --  S'Size, RM_Size should be used.
                  The_Size := RM_Size (Entity (The_Prefix));

                  Put_Line ("The size = " &
                              Int'Image
                              (UI_To_Int (The_Size)));
               else
                  The_Size := UI_From_Int (0);
                  Report_Unhandled_Node_Empty
                    (The_Entity,
                     "Do_Expression",
                     "Size attribute applied to an entity " &
                       "which is not a (sub)type or an object");
               end if;
            end;

         elsif Nkind (The_Prefix) in
           N_Indexed_Component | N_Slice
         then
            Put_Line ("Is indexed component");
            Print_Node_Briefly (Etype (Prefix (The_Prefix)));
            declare
               Array_Type : constant Entity_Id :=
                 Etype (Prefix (The_Prefix));
               Comp_Size : constant Uint :=
                 Component_Size (Array_Type);
               Default_Comp_Obj_Size : constant Uint :=
                 Esize (Prefix_Etype);
               Comp_Type_Size : constant Uint :=
                 RM_Size (Prefix_Etype);
               The_Size_To_Use : constant Uint :=
                 (if not Is_Packed_Array (Array_Type) and
                      Opt.Implicit_Packing and
                        Has_Size_Clause (Array_Type)
                  then
                     Comp_Type_Size
                  elsif UI_To_Int (Comp_Size) /= 0 then
                       Comp_Size
                  else
                     Default_Comp_Obj_Size
                 );
            begin
               Print_Node_Briefly (Array_Type);
               Put_Line ("Has size clause = "
                         & Boolean'Image
                           (Has_Size_Clause (Array_Type)));
               Put_Line ("Has pragma pack = "
                         & Boolean'Image
                           (Has_Pragma_Pack (Array_Type)));
               Put_Line ("Is packed = " &
                           Boolean'Image
                           (Is_Packed (Array_Type)));
               Put_Line ("Is packed array = " &
                           Boolean'Image
                           (Is_Packed_Array (Array_Type)));
               Put_Line ("Is bit packed = " &
                           Boolean'Image
                           (Is_Bit_Packed_Array
                              (Array_Type)));
               Put_Line ("comp type size  " &
                           Int'Image (UI_To_Int
                           (Comp_Type_Size)));
               Put_Line ("Comp_size = " &
                           Int'Image (UI_To_Int
                           (Comp_Size)));
               Put_Line ("Default_Comp_Objsize = " &
                           Int'Image (UI_To_Int
                           (Default_Comp_Obj_Size)));
               Put_Line ("The size to use = " &
                           Int'Image (UI_To_Int
                           (The_Size_To_Use)));

               The_Size := The_Size_To_Use;
            end;
         else
            --  Return the default size of the object
            Put_Line ("Any other prefix");
            Print_Node_Briefly (Etype (The_Prefix));
            The_Size := Esize (Prefix_Etype);
            Put_Line ("The size = " &
                        Int'Image (UI_To_Int (The_Size)));
         end if;
      end if;

      return Make_Constant_Expr
        (Value =>
           UI_Image (Input  => The_Size,
                     Format => Decimal),
         I_Type => Constant_Type,
         Source_Location => Get_Source_Location (N));
   end Do_Attribute_Size;

   -------------------------
   -- Has_Size_Rep_Clause --
   -------------------------

   function Has_Size_Rep_Clause (E : Entity_Id) return Boolean is
      Enty_Id : constant Symbol_Id := Intern (Unique_Name (E));
   begin
      return Extra_Entity_Info.Contains (Enty_Id) and then
        Extra_Entity_Info (Enty_Id).Specified_Rep_Size /= Uint_0;
   end Has_Size_Rep_Clause;

   ------------------
   -- Get_Rep_Size --
   ------------------

   function Get_Rep_Size (E : Entity_Id) return Uint is
      Enty_Id : constant Symbol_Id := Intern (Unique_Name (E));
   begin
      return Extra_Entity_Info (Enty_Id).Specified_Rep_Size;
   end Get_Rep_Size;

   ------------------
   -- Set_Rep_Size --
   ------------------

   procedure Set_Rep_Size (E : Entity_Id; Size : Uint) is
      Enty_Id : constant Symbol_Id := Intern (Unique_Name (E));
      Already_In_Table : constant Boolean :=
        Extra_Entity_Info.Contains (Enty_Id);
      Info : Entity_Info :=
        (if Already_In_Table then
            Extra_Entity_Info (Enty_Id)
         else
            Empty_Entity_Info);
   begin
      Info.Specified_Rep_Size := Size;
      if Already_In_Table then
         Extra_Entity_Info.Replace (Enty_Id, Info);
      else
         Extra_Entity_Info.Insert (Enty_Id, Info);
      end if;
   end Set_Rep_Size;

   -----------------------------------
   -- Has_Component_Size_Rep_Clause --
   -----------------------------------

   function Has_Component_Size_Rep_Clause (E : Entity_Id) return Boolean is
      Enty_Id : constant Symbol_Id := Intern (Unique_Name (E));
   begin
      return Extra_Entity_Info.Contains (Enty_Id) and then
        Extra_Entity_Info (Enty_Id).Specified_Rep_Component_Size /= Uint_0;
   end Has_Component_Size_Rep_Clause;

   ----------------------------
   -- Get_Rep_Component_Size --
   ----------------------------

   function Get_Rep_Component_Size (E : Entity_Id) return Uint is
      Enty_Id : constant Symbol_Id := Intern (Unique_Name (E));
   begin
      return Extra_Entity_Info (Enty_Id).Specified_Rep_Component_Size;
   end Get_Rep_Component_Size;

   ----------------------------
   -- Set_Rep_Component_Size --
   ----------------------------

   procedure Set_Rep_Component_Size (E : Entity_Id; Size : Uint) is
      Enty_Id : constant Symbol_Id := Intern (Unique_Name (E));
      Already_In_Table : constant Boolean :=
        Extra_Entity_Info.Contains (Enty_Id);
      Info : Entity_Info :=
        (if Already_In_Table then
            Extra_Entity_Info (Enty_Id)
         else
            Empty_Entity_Info);
   begin
      Info.Specified_Rep_Component_Size := Size;
      if Already_In_Table then
         Extra_Entity_Info.Replace (Enty_Id, Info);
      else
         Extra_Entity_Info.Insert (Enty_Id, Info);
      end if;
   end Set_Rep_Component_Size;

end ASVAT.Size_Model;
