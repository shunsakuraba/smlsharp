(**
 * Converter from AbstractInstruction2 to LLVM
 * @copyright (c) 2012, Shun Sakuraba
 * @author Shun SAKURABA
 *)

structure LLVMEmit = 
struct

structure A = AbstractInstruction2
structure L = LLVM

exception NotImplemented
exception LLVMError of string

type renameEnv = (string * L.ty) SEnv.map

local 

(* FIXME: I will regret these hacks. Should have used writer monad ... *)
val toplevelDecls : L.globalEntry list ref = ref []
fun pushToplevelDecls decl = 
    toplevelDecls := decl :: !toplevelDecls

val blockPrologueInsns : L.instruction list ref = ref []

fun pushBlockPrologue insn = 
    blockPrologueInsns := insn :: !blockPrologueInsns

fun clearBlockPrologue () = 
    blockPrologueInsns := []

fun flushBlockPrologue () = 
    let val ret = List.rev (!blockPrologueInsns) in
      ( clearBlockPrologue ();
        ret )
    end

fun printASInstruction i =
    print
      (Control.prettyPrint
         (A.format_instruction i))

fun printInstruction i = 
    print
      (Control.prettyPrint
         (L.format_instruction i))

fun printInstructions is = 
    app printInstruction is
    
fun printBasicBlock b =
    print 
      (Control.prettyPrint 
         (L.format_basicBlock b))

fun printGlobalEntry g =
    print 
      (Control.prettyPrint 
         (L.format_globalEntry g))

fun printGlobalEntries gs =
    app printGlobalEntry gs

fun genLocalName () = 
    "t" ^ VarID.toString (VarID.generate ())

(* FIXME TODO: platform-dependent! *)
val platform_integer = L.I32

fun translateType (A.GENERIC id) = L.POINTER (L.INTEGER platform_integer)
  | translateType A.UINT = L.INTEGER platform_integer
  | translateType A.SINT = L.INTEGER platform_integer
  | translateType A.BYTE = L.INTEGER L.I8
  | translateType A.BOXED = L.POINTER (L.INTEGER platform_integer)
  | translateType A.HEAPPOINTER = L.POINTER (L.INTEGER platform_integer)
  | translateType A.CODEPOINTER = L.POINTER (L.INTEGER platform_integer)
  | translateType A.CPOINTER = L.POINTER (L.INTEGER platform_integer)
  | translateType A.ENTRY = L.POINTER (L.TYSTRUCT [L.INTEGER platform_integer,
                                                   L.POINTER (L.INTEGER platform_integer)]) (* TODO: ENTRY *)
  | translateType A.FLOAT = L.FLOAT
  | translateType A.DOUBLE = L.DOUBLE

val boxedType = translateType A.BOXED

(* No need to do something special, since it is already alpha converted ... *)
fun emitVarName ({ id = id, ty = ty, displayName = displayName } : A.varInfo) = 
    "v" ^ VarID.toString id

fun emitVarInfo v =
    L.LOCAL (emitVarName v)

fun emitArgName { id = id, ty = ty, argKind = argKind } = 
    "a" ^ VarID.toString id

fun emitArgInfo a =
    L.LOCAL (emitArgName a)

fun emitLabel label = 
    "L" ^ VarID.toString label

fun emitLabelVar label = 
    L.LOCAL (emitLabel label)

fun emitClusterName cl = 
    "C" ^ ClusterID.toString cl

fun emitBlockName cluster label = 
    emitClusterName cluster ^ "_" ^ emitLabel label

fun emitConstantName c = 
   "c" ^ VarID.toString c

fun emitValue _ (A.UInt x) = L.IMM (L.UINT (A.Target.UInt.toInt x))
  | emitValue _ (A.SInt x) = L.IMM (L.SINT (A.Target.SInt.toInt x))
  | emitValue _ (A.Byte x) = L.IMM (L.UINT (A.Target.UInt.toInt x))
  | emitValue _ (A.Var v) = L.LOCAL (emitVarName v)
  | emitValue _ A.Nowhere = L.IMM (L.SINT 0)
  | emitValue _ A.Null = L.IMM (L.SINT 0)
  | emitValue _ A.Empty = L.IMM L.NULL
  | emitValue ty (A.Const c) =
    let val id = genLocalName ()
        val () = pushBlockPrologue
                   (L.LOAD { res = id, 
                             ty = translateType ty,
                             arg = L.GLOBAL (emitConstantName c) })
    in 
      L.LOCAL id
    end
  | emitValue _ (A.Init id) = L.LOCAL ("i" ^ VarID.toString id)
  | emitValue _ (A.Entry {clusterId = cid, entry = label} ) = 
    L.GLOBAL (emitBlockName cid label)
  | emitValue _ (A.Global (_, _)) = raise Control.Bug "emitValue Global"
  | emitValue _ (A.Extern (_, _)) = raise Control.Bug "emitValue Extern"
  | emitValue _ (A.Label _) = raise Control.Bug "emitValue Label"
  | emitValue _ (A.ExtFunLabel l) = 
    ( pushToplevelDecls 
         (L.DECLFUN { rettype = L.VOID,
                      name = l,
                      argtypes = [] });
      L.GLOBAL l )
                           
fun emitImmZero ty = 
    L.IMM (L.SINT 0)

fun emitImmInt ty n = 
    L.IMM (L.SINT n)

fun emitFunctionArguments args tys = 
    ListPair.map 
      (fn (ar, ty) => (emitArgInfo ar, translateType ty))
      (args, tys)

fun emitDeclarations clusterName {label = label, blockKind = blockKind} = 
    case blockKind of 
      A.Basic => NONE
    | A.Branch => NONE
    | A.Merge => NONE
    | A.Loop => NONE
    | A.LocalCont => NONE
    | A.Handler _ => NONE
    | A.CheckFailed => NONE
    | A.FunEntry { argTyList = argTys,
                   resultTyList = [resTy], (* FIXME: why is this a list ?? *)
                   env = _,
                   argVarList = _ }
      => SOME (L.DECLFUN { rettype = translateType resTy,
                           name = emitBlockName clusterName label,
                           argtypes = List.map translateType argTys })
    | A.FunEntry _ 
      => raise Control.Bug ("Unexpected: LLVM.emitDeclarations, FunEntry.resultTyList is not a single element")
    | A.CodeEntry 
      => SOME (L.DECLFUN { rettype = L.VOID,
                           name = emitBlockName clusterName label,
                           argtypes = [] })
    | A.ExtFunEntry { argTyList = argTys,
                      resultTyList = [resTy], (* FIXME: why is this a list ?? *)
                      env = _,
                      argVarList = _,
                      attributes = attrs }
      (* FIXME TODO: attributes *)
      => SOME (L.DECLFUN { rettype = translateType resTy,
                           name = emitBlockName clusterName label,
                           argtypes = List.map translateType argTys })
    | A.ExtFunEntry _ 
      => raise Control.Bug ("Unexpected: LLVM.emitDeclarations, ExtFunEntry.resultTyList is not a single element")

fun emitPrimOp1 dst op1 arg retty argty = 
    let 
      val arg = emitValue argty arg
      fun lltype ty1 ty2 errmsg =
          let
            val llty = translateType ty1
            val llty2 = translateType ty2
          in
            if llty <> llty2 
            then raise (LLVMError (errmsg ^ "type mismatch")) 
            else llty
          end
    in
    case op1 of
      (* LLVM does not support unary NEG, see "sub" instruction in the reference *)
      A.Neg => 
      let val llty = lltype retty argty "Neg" in
        [L.BINOP { res = dst,
                   ty = llty,
                   binOpKind = L.SUB,
                   arg1 = emitImmZero llty,
                   arg2 = arg }]
      end
    | A.Abs =>
      (* abs(x) = (x + (x >> 31)) ^ (x >> 31) for 32-bit env *)
      raise NotImplemented
    | A.Cast =>
      (* "bitcast" *)
      raise NotImplemented
    | A.SignExt =>
      (* "sext" insn *)
      raise NotImplemented
    | A.ZeroExt =>
      (* "zext" insn *)
      raise NotImplemented
    | A.Notb =>
      (* LLVM does not support unary NOT, see "xor" instruction in the reference *)
      let val llty = lltype retty argty "Notb" in
        [L.BINOP { res = dst,
                   ty = llty,
                   binOpKind = L.XOR,
                   arg1 = emitImmInt llty ~1,
                   arg2 = arg }]
      end
    | A.PayloadSize =>
      raise NotImplemented
    end

fun emitPrimOp2 dst op2 arg1 arg2 retty arg1ty arg2ty = 
    let 
      val arg1 = emitValue arg1ty arg1
      val arg2 = emitValue arg2ty arg2
      val arg1ll = translateType arg1ty
      val arg2ll = translateType arg2ty
      val retll = translateType retty
      val isFloat = 
          case retll of
            L.FLOAT => true
          | L.DOUBLE => true
          | _ => false
      val isSigned1 = 
          case arg1ty of
            A.UINT => false
          | _ => true
      fun binop2direct errmsg bop =
          let val llty =
                  let val optype = 
                          if arg1ll <> arg2ll
                          then raise Control.Bug ("Type mismatch: emitPrimOp2: " ^ errmsg)
                          else arg1ll
                  in
                    optype
                  end
          in
            [ L.BINOP { res = dst,
                        ty = llty,
                        binOpKind = bop,
                        arg1 = arg1,
                        arg2 = arg2 }]
          end
          fun cmpint optype = 
              let val () = 
                      if arg1ll <> arg2ll 
                      then raise Control.Bug ("Type mismatch: emitPrimOp2/cmpint") 
                      else ()
              in
                [ L.BINOP { res = dst,
                            ty = arg1ll,
                            binOpKind = L.ICMP optype,
                            arg1 = arg1, 
                            arg2 = arg2 }]
              end
          fun cmpfloat optype =
              let val () = 
                      if arg1ll <> arg2ll 
                      then raise Control.Bug ("Type mismatch: emitPrimOp2/cmpint")
                      else ()
              in
                [ L.BINOP { res = dst,
                            ty = arg1ll,
                            binOpKind = L.FCMP optype,
                            arg1 = arg1, 
                            arg2 = arg2 }]
              end
    in
      case (op2, isFloat, isSigned1) of 
        (A.Add, true, _) => binop2direct "Add" L.FADD
      | (A.Add, false, _) => binop2direct "Add" L.ADD
      | (A.Sub, true, _) => binop2direct "Sub" L.FSUB
      | (A.Sub, false, _) => binop2direct "Sub" L.SUB
      | (A.Mul, true, _) => binop2direct "Mul" L.FMUL
      | (A.Mul, false, _) => binop2direct "Mul" L.MUL
      (* Div == x / y rounding towards negative infinity
         Mod == x % y rounding towards negative infinity
         Quot == x / y rouding towards zero (matches to sdiv)
         Rem == x % y rouding towards zero (matches to srem)
         Quot / Rem is never applied on floating values (as far as I read in X86Select.sml.)
         Div / Mod operation is by far complex than Quot / Rem. See X86Select.divmod for details.
       *)
      | (A.Div, true, _) => binop2direct "Div" L.FDIV
      | (A.Div, false, true) => raise NotImplemented (*FIXME*)
      | (A.Div, false, false) => binop2direct "Div" L.UDIV
      | (A.Mod, true, _) => raise NotImplemented (*FIXME*)
      | (A.Mod, false, true) => raise NotImplemented (*FIXME*)
      | (A.Mod, false, false) => binop2direct "Mod" L.UREM
      | (A.Quot, false, true) => binop2direct "Quot" L.SDIV
      | (A.Quot, false, false) => binop2direct "Quot" L.UDIV
      | (A.Rem, false, true) => binop2direct "Rem" L.SREM
      | (A.Rem, false, false) => binop2direct "Rem" L.UREM
      | (A.Lt, true, _) => cmpfloat L.FOLT
      | (A.Lt, false, true) => cmpint L.SLT
      | (A.Lt, false, false) => cmpint L.ULT
      | (A.Gt, true, _) => cmpfloat L.FOGT
      | (A.Gt, false, true) => cmpint L.SGT
      | (A.Gt, false, false) => cmpint L.UGT
      | (A.Lteq, true, _) => cmpfloat L.FOLE
      | (A.Lteq, false, true) => cmpint L.SLE
      | (A.Lteq, false, false) => cmpint L.ULE
      | (A.Gteq, true, _) => cmpfloat L.FOGE
      | (A.Gteq, false, true) => cmpint L.SGE
      | (A.Gteq, false, false) => cmpint L.UGE
      | (A.MonoEqual, true, _) => cmpfloat L.FOEQ
      | (A.MonoEqual, false, _) => cmpint L.EQ
      | (A.UnorderedOrEqual, true, _) => cmpfloat L.FUEQ 
      | (A.Andb, false, _) => binop2direct "Andb" L.AND
      | (A.Orb, false, _) => binop2direct "Orb" L.OR
      | (A.Xorb, false, _) => binop2direct "Xorb" L.XOR
      | (A.LShift, false, _) => binop2direct "LShift" L.SHL 
      | (A.RShift, false, _) => binop2direct "RShift" L.LSHR
      | (A.ArithRShift, false, _) => binop2direct "ArithRShift" L.ASHR
      | (A.PointerAdvance, false, _) => raise NotImplemented (* GEP *)
      | _ => raise Control.Bug ("emitBinOp2")
    end

fun emitCast { res, fromty, value, toty } =
    [L.UNOP { res = res,
              ty = fromty,
              outty = toty,
              unOpKind = L.BITCAST,
              arg = value }]
               
fun emitInstruction insn =
    case insn of 
      A.Move { dst = dst, 
               ty = ty,
               value = value,
               loc = loc } 
      => emitCast { res = emitVarName dst,
                    fromty = translateType ty,
                    value = emitValue ty value,
                    toty = translateType ty }
    | A.Load { dst = dst,
               ty = ty,
               block = block,
               offset = offset,
               size = size,
               loc = loc } => raise Control.Bug "Not Implemented: Load"
    | A.Update { block = block,
                 offset = offset,
                 ty = ty,
                 size = size,
                 value = value,
                 barrier = barrier,
                 loc = loc } => raise Control.Bug "Not Implemented: Update"
    | A.Get { dst = dst,
              ty = ty,
              src = src,
              loc = loc } 
      => emitCast { res = emitVarName dst,
                    fromty = translateType ty,
                    value = emitArgInfo src,
                    toty = translateType ty }
    | A.Set { dst = dst,
              ty = ty,
              value = value, 
              loc = loc } 
      => [L.UNOP { res = emitArgName dst,
                   ty = translateType ty,
                   outty = translateType ty,
                   unOpKind = L.BITCAST,
                   arg = emitValue ty value }]
    | A.Alloc { dst = dst, 
                objectType = objectType,
                bitmaps = bitmaps,
                payloadSize = payloadSize,
                loc = loc } => raise NotImplemented
    | A.PrimOp1 { dst = dst,
                  op1 = (op1, argty, retty), 
                  arg = arg,
                  loc = loc }
      => emitPrimOp1 (emitVarName dst) op1 arg retty argty
    | A.PrimOp2 { dst = dst,
                  op2 = (op2, argty1, argty2, retty),
                  arg1 = arg1,
                  arg2 = arg2,
                  loc = loc } 
      => emitPrimOp2 (emitVarName dst) op2 arg1 arg2 retty argty1 argty2
    | A.CallExt { dstVarList = [dstVar],
                  entry = entry,
                  attributes = attributes,
                  argList = argList,
                  calleeTy = (argTys, [retTy]),
                  loc = loc } =>
      let val tmpreg = genLocalName ()
          val resty_ll = translateType retTy
          val argtys_ll = map translateType argTys
      in
        [ L.UNOP { res = tmpreg,
                   ty = L.POINTER (L.FUNCTION { rettype = L.VOID,
                                                argtypes = [] }),
                   outty = L.POINTER (L.FUNCTION { rettype = resty_ll,
                                                   argtypes = argtys_ll }),
                   unOpKind = L.BITCAST,
                   arg = emitValue A.ENTRY entry },
          L.CALL { res = SOME (emitArgName dstVar), 
                   resty = resty_ll,
                   func = L.LOCAL tmpreg,
                   args = emitFunctionArguments argList argTys,
                   isFastCC = false,
                   isTail = false }]
      end
    | A.CallExt _ => raise Control.Bug "Not Impelented: CallExt"
    | A.Call { dstVarList = [dstVar],
               entry,
               env,
               argList,
               argTyList,
               resultTyList = [retTy],
               loc = loc } =>
      [ L.CALL { res = SOME (emitArgName dstVar), 
                 resty = translateType retTy,
                 func = emitValue A.ENTRY entry,
                 args = emitFunctionArguments argList argTyList,
                 isFastCC = true,
                 isTail = false }]
    | A.Call _ => 
      raise Control.Bug "Not Implemented: Call multiple ret"
    | A.TailCall { entry = entry,
                   env = env,
                   argList = argList,
                   argTyList = argTyList,
                   resultTyList = [resultTy],
                   loc = loc } =>
      let
        val tmpreg = genLocalName ()
      in
        [ L.CALL { res = SOME tmpreg, 
                   resty = translateType resultTy,
                   func = emitValue A.ENTRY entry,
                   args = emitFunctionArguments argList argTyList,
                   isFastCC = true,
                   isTail = true },
          L.RET { retty = translateType resultTy,
                  retval = SOME (L.LOCAL tmpreg) }]
      end
    | A.TailCall _ =>
      raise Control.Bug "TODO Implement: multiple value ret"
    | A.CallbackClosure { dst = dst,
                          entry = entry,
                          env = env, 
                          exportTy = (argTys, retTys),
                          attributes = attributes,
                          loc = loc } => raise NotImplemented
    | A.Return { varList = [var],
                 argTyList = argTyList,
                 retTyList = [retTy],
                 loc = loc } 
      => [ L.RET 
             { retty = translateType retTy,
               retval = SOME (emitArgInfo var) } ]
    | A.Return _ 
      => raise Control.Bug "Multiple return args"
    | A.ReturnExt { varList = [],
                    argTyList = argTyList,
                    retTyList = [],
                    attributes = attributes,
                    loc = loc } 
      => [ L.RET { retty = L.VOID,
                   retval = NONE } ]
    | A.ReturnExt _ => raise Control.Bug "Implement ReturnExt"
    | A.If { value1 = value1,
             value2 = value2,
             loc = loc,
             op2 = (op2, arg1Ty, arg2Ty, retTy),
             thenLabel = thenLabel,
             elseLabel = elseLabel } 
      => let 
        val tmpreg = genLocalName ()
        val compareOps = emitPrimOp2 tmpreg op2 value1 value2 retTy arg1Ty arg2Ty
        val branchOps = 
            [ L.BRANCH  
                { condition = (L.LOCAL tmpreg), 
                  labelIf = emitLabel thenLabel,
                  labelElse = emitLabel elseLabel } ]
      in
        compareOps @ branchOps
      end
    | A.CheckBoundary { offset = offset,
                        size = size, 
                        objectSize = objectSize,
                        passLabel = passLabel,
                        failLabel = failLabel,
                        loc = loc } => raise NotImplemented
    | A.Raise { exn = exn,
                loc = loc } => raise NotImplemented
    | A.RaiseExt { exn = exn,
                   attributes = attributes,
                   loc = loc } => (* FIXME TODO *)
      [ L.UNREACHABLE ]
    | A.Jump { label = label,
               knownDestinations = knownDestinations,
               loc = loc } =>
      let
        fun bug () = 
            raise Control.Bug "Unreasonable desitination at Jump operator"
        val jumpto = 
            case label of 
              A.UInt _ => bug () 
            | A.SInt _ => bug ()
            | A.Byte _ => bug ()
            | A.Var _ => bug ()
            | A.Nowhere => bug ()
            | A.Null => bug ()
            | A.Empty => bug ()
            | A.Const _ => bug ()
            | A.Init _ => bug ()
            | A.Entry _ => raise NotImplemented
            | A.Global _ => raise NotImplemented
            | A.Extern _ => bug ()
            | A.Label l => emitLabel l
            | A.ExtFunLabel _ => bug ()
      in
        [ L.JUMP { label = jumpto } ]
      end
    | A.ChangeHandler { change,
                        previousHandler,
                        newHandler,
                        tryBlock,
                        loc } => 
      (* FIXME TODO *)
      [ L.JUMP { label = (emitLabel tryBlock) } ]

(* FIXME TODO: add env and phi functions *)
fun emitBlockHeader A.Basic = []
  | emitBlockHeader A.Branch = []
  | emitBlockHeader A.Merge = []
  | emitBlockHeader A.Loop = []
  | emitBlockHeader A.LocalCont = []
  | emitBlockHeader (A.Handler arg) =
    let val resname = emitArgName arg
        val { id, ty, argKind } = arg
    in
      (* FIXME TODO *)
      [L.UNOP { res = resname, 
                ty = translateType ty,
                outty = translateType ty,
                unOpKind = L.BITCAST,
                arg = L.IMM L.NULL }]
    end
  | emitBlockHeader (A.FunEntry _) = []
  | emitBlockHeader A.CodeEntry = []
  | emitBlockHeader (A.ExtFunEntry _) = []
  | emitBlockHeader A.CheckFailed = []

fun emitBasicBlock { label = label,
                     blockKind = blockKind, 
                     handler = handler,
                     instructionList = insns,
                     loc = loc } =
    { blockname = emitLabel label,
      instructions = 
      let 
        val header = emitBlockHeader blockKind
        val () = clearBlockPrologue ()
        val insns = 
            List.concat
              (map 
                 (fn is =>
                     let
                       (* val _ = printASInstruction is *)
                       val r = emitInstruction is 
                       (* val _ = printInstructions r *) 
                     in
                       r
                     end)
                 insns)
        val prologue = flushBlockPrologue ()
      in
        header @ prologue @ insns
      end
    } : L.basicBlock

fun emitFunbody blocks =
    { basicBlocks = List.map emitBasicBlock blocks }

fun emitCluster { frameBitmap = fbs,
                  name = clusterName, 
                  body,
                  loc } = 
    (* find fun entry blocks and declare *)
    let
      val blockKindsLabels = 
          List.map
          (fn { label = label, 
                blockKind,
                handler,
                instructionList,
                loc } => (label, blockKind))
          body
      val funEntries = 
          List.concat 
            (List.map
               (fn (l, k) =>
                   case k of
                     A.Basic => []
                   | A.Branch => []
                   | A.Merge => []
                   | A.Loop => []
                   | A.LocalCont => []
                   | A.Handler _ => []
                   | A.CheckFailed => []
                   | A.FunEntry _ => [(l, k)]
                   | A.CodeEntry => [(l, k)]
                   | A.ExtFunEntry _ => [(l, k)])
               blockKindsLabels)

    (* from each function entry, DFS blocks to decide which code passes are to be visited. Also get cluster's return value type. *)

    (* emit each function entry tracking down DFS results *)

    (* emit real function entry *)
    in
      case funEntries of 
        [(l, A.FunEntry 
               { argTyList = argTyList, 
                 resultTyList = [resTy], 
                 env = env,
                 argVarList = argVarList })] =>
        let val r = L.DEFFUN 
                      { rettype = translateType resTy,
                        name = emitBlockName clusterName l,
                        args = ListPair.map 
                                 (fn (ar, ty) 
                                     => (emitArgName ar, translateType ty))
                                 (argVarList, argTyList),
                        funbody = emitFunbody body, 
                        isFastCC = true} 
            (* val _ = printGlobalEntry r *)
        in
          r
        end
      | [(_, A.FunEntry f)] => raise Control.Bug "Implement returning multiple values"
      | [(_, A.CodeEntry)] => raise Control.Bug "Implement CodeEntry"
      | [(l, A.ExtFunEntry
               { argTyList,
                 resultTyList = [],
                 env,
                 argVarList,
                 attributes })] => 
        let val r = L.DEFFUN
                      { rettype = L.VOID,
                        name = emitBlockName clusterName l,
                        args = ListPair.map
                                 (fn (ar, ty) 
                                     => (emitArgName ar, translateType ty))
                                 (argVarList, argTyList),
                        funbody = emitFunbody body,
                        isFastCC = false }
            (* val _ = printGlobalEntry r *)
        in
          r
        end
      | [(_, A.ExtFunEntry _)] => 
        raise Control.Bug "Implement returning multiple values @ ExtFunEntry"
      | _ => raise Control.Bug "Implement Multiple funentry"
    end

fun emitClusters clusters = 
    List.map emitCluster clusters

fun emitData (A.PrimData prim) = emitPrimData prim
  | emitData (A.StringData s) 
    = (* FIXME: this hack is required to compensate the type difference.
       *)
    let val tmpval = genLocalName ()
        val strty = L.ARRAY { elemty = L.INTEGER L.I8,
                              size = String.size s + 1 }
        val () = pushToplevelDecls 
                   (L.DECVAL { name = tmpval,
                               ty = strty,
                               value = L.CONSTSTRING (s ^ "\000") })
    in
      (* FIXME: need clean-up *)
      (boxedType,
       L.CONSTEXPR 
         (L.CONSTUNOP 
            { constant = L.CONSTEXPR 
                           (L.CONSTGEP 
                              { ty = L.POINTER strty,
                                constant = L.CONSTGLOBAL tmpval,
                                indices = [ (L.INTEGER L.I32, L.UINT 0),
                                            (L.INTEGER L.I32, L.UINT 0) ] }),
              unOpKind = L.BITCAST,
              fromty = L.POINTER (L.INTEGER L.I8),
              toty = boxedType } ))
    end
  | emitData (A.IntInfData inf) = raise Control.Bug "Implement IntInfData (i.e Bigint)"
  | emitData (A.ObjectData obj) = emitObjectData obj
  | emitData (A.VarSlot _) = raise Control.Bug "Implemnt VarSlot"
and emitPrimData (A.UIntData u) =
    (L.INTEGER platform_integer, L.UINT (A.Target.UInt.toInt u))
  | emitPrimData (A.SIntData s) =
    (L.INTEGER platform_integer, L.SINT (A.Target.SInt.toInt s))
  | emitPrimData (A.ByteData u) =
    (L.INTEGER L.I8, L.UINT (A.Target.UInt.toInt u))
  | emitPrimData (A.RealData r) = 
    (L.DOUBLE, raise Control.Bug "Implement PrimData RealData (check why this is string)")
  | emitPrimData (A.FloatData f) =
    (L.FLOAT, raise Control.Bug "Implement PrimData FloatData (check why this is string)")
  | emitPrimData (A.EntryData { clusterId, entry }) =
    (* FIXME TODO *)
    (L.POINTER (L.INTEGER platform_integer), L.NULL)
  | emitPrimData (A.ExternLabelData global) =
    raise Control.Bug "Not implemented: ExternLabelData"
  | emitPrimData A.NullBoxedData = 
    (L.POINTER (L.INTEGER platform_integer), L.NULL)
  | emitPrimData _ = raise Control.Bug "Not Impelemented: PrimData"
and emitObjectData { objectType, bitmaps, payloadSize, fields } = 
    let val llfields = 
            List.map (fn {size, value} => emitPrimData value) fields
    in
      case objectType of
        A.Array => raise Control.Bug "Implement Array"
      | A.Vector => raise Control.Bug "Implement Vector"
      | A.Record {mutable} => 
        (L.TYSTRUCT (#1 (ListPair.unzip llfields)), L.CONSTSTRUCT llfields)
    end


fun emitConstant id data = 
    let val (ty, d) = emitData data 
        val ret = 
            L.DECVAL 
              { name = emitConstantName id,
                ty = ty,
                value = d }
        (* val _ = printGlobalEntry ret *)
    in
      ret
    end
    
fun emitConstants constants = 
    VarID.Map.foldli (fn (k, c, ls) => emitConstant k c :: ls) [] constants

(* TODO: mainSymbol *)
fun emitToplevel mainSymbol NONE = []
  | emitToplevel mainSymbol (SOME { clusterId = clusterId, entry = entry } ) = 
    let val main = 
            { basicBlocks = [
              { blockname = "mainblock", 
                instructions = [
                L.CALL { res = NONE,
                         resty = L.VOID,
                         args = [],
                         func = L.GLOBAL (emitBlockName clusterId entry),
                         isFastCC = false,
                         isTail = false },
                L.RET { retty = L.INTEGER platform_integer,
                        retval = SOME (L.IMM (L.SINT 0)) }
                ] }
              ] }
        val toplevel = L.DEFFUN 
                         { rettype = L.INTEGER platform_integer,
                           name = "main",
                           args = [],
                           funbody = main,
                           isFastCC = false }
    in
      [toplevel]
    end
    
in

fun emit {mainSymbol: string} (absprog:AbstractInstruction2.program) =
    (* for prototyping ... *)
    let val prog = 
            case absprog of 
              { clusters,
                constants,
                globals = _,
                toplevel } =>
              let val () = toplevelDecls := []
                  val funcs = emitClusters clusters
                  val consts = emitConstants constants
                  val main = emitToplevel mainSymbol toplevel
                  val addenda = !toplevelDecls
                  val () = toplevelDecls := []
              in
                funcs @ consts @ main @ addenda
              end
        val _ = printGlobalEntries prog
    in
      prog
    (* convert constants *)
    (* *)
    (* #toplevel absprog *)
    (* #clusters *)
    (* #constants *)
    (* #globals *)

    end

end (* local *)
end (* struct *)
