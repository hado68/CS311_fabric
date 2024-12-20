package cs320

object Implementation extends Template {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)

  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)

  object T {
    import Typed._

    case class TypeName(name: String)
    type TypeEnv = Map[Any, Any]

    def substitute(vartype: Type, map: Map[String, Type]): Type = vartype match {
      case AppT(x, targs) => {
        val subtargs = targs.foldLeft(List[Type]()) { (acc, targ) =>
          acc :+ substitute(targ, map)
        }
        AppT(x, subtargs)
      }
      case VarT(name) => {
        if (map.contains(name)){
          map(name)
        }else{
          vartype
        }
      }    
      case IntT => vartype
      case BooleanT => vartype
      case UnitT => vartype
      case ArrowT(ptypes, rtype) => {
        val subptypes = ptypes.foldLeft(List[Type]()) { (acc, ptype) =>
          acc :+ substitute(ptype, map)
        }
        val subrtype = substitute(rtype, map)
        ArrowT(subptypes, subrtype)
      }
    }

    def mustSame(left: Type, right: Type): Type =
      if (same(left, right)) left
      else notype(s"$left is not equal to $right")

    def same(left: Type, right: Type): Boolean =
      (left, right) match {
        case (IntT, IntT) => true
        case (BooleanT, BooleanT) => true
        case (UnitT, UnitT) => true
        case (AppT(_, ltargs), AppT(_, rtargs)) => ltargs == rtargs      
        case (VarT(x), VarT(y)) => x == y
        case (ArrowT(p1, r1), ArrowT(p2, r2)) =>
          if (p1 == p2){
            r1 == r2
          }else{
            false
          }
        case _ => false
      }

    def notype(msg: Any): Nothing = error(s"no type: $msg")

    def wellform(t: Type, tenv: TypeEnv): Type = t match {
      case AppT(name, targs) => {
        for (targ <- targs){
          wellform(targ, tenv)
        }
        if (tenv.contains(TypeName(name))){
          tenv(TypeName(name)) match{
            case TypeDef(name, tparams, variants) => {
              if (tparams.length == targs.length){
                t
              }else{
                error("length is different")
              }
            }
            case _ => error("type is not match")
          }          
        }else{
          error("not in tenv")
        }
      }
      case VarT(name) => {
        if (tenv.contains(t)){
          t
        }else{
          error("not in tenv")
        }
      }
      case IntT => t
      case BooleanT => t
      case UnitT => t
      case ArrowT(ptypes, rtype) => {
        for (types <- ptypes){
          wellform(types, tenv)
        }
        wellform(rtype, tenv)
        t
      }
    }

    def wellformrec(t: RecDef, tenv: TypeEnv): RecDef = t match {
      case Lazy(name, typ, expr) =>{
        wellform(typ,tenv)
        mustSame(typ, typeCheck(expr, tenv))
        t
      }
      case RecFun(name, tparams, params, rtype, body) => {
        for (param <- tparams){
          if (tenv.contains(VarT(param))){
            error("it can't be in tenv")
          }
        }
        val tenv2 = tparams.foldLeft(tenv) { (currentTenv, param) =>
          currentTenv + (VarT(param) -> None)
        }
        for (param <- params){
          wellform(param._2, tenv2)
        }
        wellform(rtype, tenv2)
        val tenvi = params.foldLeft(tenv2) { (currentTenv, param) =>
          currentTenv + (param._1 -> ((param._2, Nil), false))
        } 
        val etype = typeCheck(body, tenvi)
        mustSame(etype, rtype)
        t
      }
      case TypeDef(name, tparams, variants) =>{
        for (param <- tparams){
          if (tenv.contains(VarT(param))){
            error("it can't be in tenv")
          }
        }
        val tenv2 = tparams.foldLeft(tenv) { (currentTenv, param) =>
          currentTenv + (VarT(param) -> None)
        }
        for (variant <- variants){
          for (param <- variant.params){
            wellform(param, tenv2)
          }
        }        
        t
      }
    }

    def casetypeCheck(c: Case, tenv: TypeEnv, variants: List[Variant], params: List[String], types: List[Type]): Type = {
      if (params.length == types.length){
        val w = variants.foldLeft(None: Option[Variant]) { (current, wi) => current match{
          case Some(wi) => current
          case None => if (wi.name == c.variant){
            Some(wi)
          }else{
            None
          }
        }}
        w match{
          case Some(w) => {
            if(w.params.length == c.names.length){
            val updates = w.params.zipWithIndex.map { case (param, idx) =>
              c.names(idx) -> ((substitute(param, (params zip types).toMap), Nil), false)
            }.toMap
            val nenv = tenv ++ updates
              typeCheck(c.body, nenv)
            }else{
              error("length is different")
            }
          }
          case _ => error("no identical name")
        }
      }else{
        error("length is different")
      }
    }

    def typeCheck(expr: Expr, tenv: TypeEnv): Type = expr match {
      case Id(name, targs) =>
        for (arg <- targs){
          wellform(arg, tenv)
        }
        if (tenv.contains(name)){
          tenv(name) match {
            case (scheme: (Type, List[VarT]), bool: Boolean) => {
              if (scheme._2.length == targs.length){
                substitute(scheme._1, (scheme._2.map(_.name) zip targs).toMap)
              }else{
                error("length is different")
              }              
            }
            case _ => error("not a scheme")
          }          
        }else{
          error("name is not in tenv")
        }
      case IntE(value) => IntT
      case BooleanE(value) => BooleanT
      case UnitE => UnitT
      case Add(left, right) =>
        mustSame(typeCheck(left, tenv), IntT)
        mustSame(typeCheck(right, tenv), IntT)
        IntT
      case Mul(left, right) =>
        mustSame(typeCheck(left, tenv), IntT)
        mustSame(typeCheck(right, tenv), IntT)
        IntT
      case Div(left, right) =>
        mustSame(typeCheck(left, tenv), IntT)
        mustSame(typeCheck(right, tenv), IntT)
        IntT
      case Mod(left, right) =>
        mustSame(typeCheck(left, tenv), IntT)
        mustSame(typeCheck(right, tenv), IntT)
        IntT
      case Eq(left, right) =>
        mustSame(typeCheck(left, tenv), IntT)
        mustSame(typeCheck(right, tenv), IntT)
        BooleanT
      case Lt(left, right) =>
        mustSame(typeCheck(left, tenv), IntT)
        mustSame(typeCheck(right, tenv), IntT)
        BooleanT
      case Sequence(left, right) =>
        typeCheck(left, tenv)
        typeCheck(right, tenv)
      case If(cond, texpr, fexpr) =>
        mustSame(typeCheck(cond, tenv), BooleanT)
        mustSame(typeCheck(texpr, tenv), typeCheck(fexpr, tenv))
      case Val(mut, name, typ, expr, body) => typ match {
        case Some(t) => 
          wellform(t, tenv)
          mustSame(typeCheck(expr, tenv), t)
          typeCheck(body, tenv + (name -> ((typeCheck(expr, tenv), Nil), mut)))
        case None => typeCheck(body, tenv + (name -> ((typeCheck(expr, tenv), Nil), mut)))
      }
      case RecBinds(defs, body) => {
        val tenvn = defs.foldLeft(tenv){(currentTenv, di) =>
          val tenvi = createtenv(di, tenv)
          currentTenv ++ tenvi
        }
        for (di <- defs){
          wellformrec(di, tenvn)
        }
        wellform(typeCheck(body, tenvn), tenv)
      }
      case Fun(params, body) => {
        for (param <- params){
          wellform(param._2, tenv)
        }
        val tenv2 = params.foldLeft(tenv){(currentTenv, param) => currentTenv + (param._1 -> ((param._2, Nil), false))}
        ArrowT(params.map(_._2), typeCheck(body, tenv2))
      }
      case Assign(name, expr) =>{
        if (tenv.contains(name)){
          tenv(name) match{
            case (scheme: (Type, List[VarT]), bool: Boolean) => if (scheme._2.length == 0){
              if (bool){
                mustSame(scheme._1, typeCheck(expr, tenv))
                UnitT
              }else{
                error("mut is not var")
              }
            }else{
              error("length is not zero")
            }
            case _ => error("not type sceheme")
          }
        }else{
          error("name is not in tenv")
        }
      }
      case App(f, args) => {
        typeCheck(f, tenv) match{
          case ArrowT(ptypes, rtype) => {
            if (args.length == ptypes.length){
              val zip = (ptypes zip args) 
              for (z <- zip){
                mustSame(z._1, typeCheck(z._2, tenv))
              }
              rtype
            }else{
              error("length is different")
            }
          }
          case _ => error("not Arrow type")
        }
      }
      case Match(expr, cases) => {
        typeCheck(expr, tenv) match{
          case AppT(t, targs) => {
            if(tenv.contains(TypeName(t))){
              tenv(TypeName(t)) match{
                case TypeDef(name, tparams, variants) => {
                  if (targs.length == tparams.length){
                    if (cases.length == variants.length){
                      val t1 = casetypeCheck(cases(0), tenv, variants, tparams, targs)
                      for (c <- cases){
                        mustSame(t1, casetypeCheck(c, tenv, variants, tparams, targs))
                      }
                      t1
                    }else{
                      error("length is different")
                    }
                  }else{
                    error("length is different")
                  }
                }
                case _ => error("not type definition")
              }
            }else{
              error("not in tenv")
            }
          }
          case _ => error("not a type application")
        }
      }
    }

    def createtenv(di: RecDef, tenv : TypeEnv): TypeEnv = {
      di match{
        case Lazy(name, typ, expr) =>  Map(name -> ((typ, Nil), false))
        case RecFun(name, tparams, params, rtype, body) => Map(name -> ((ArrowT(params.map(_._2), rtype), tparams.map(param => VarT(param))), false))
        case TypeDef(name, tparams, variants) => {
          if (tenv.contains(TypeName(name))){
            error("must not in tenv")
          }
          val newtenv: TypeEnv = Map(TypeName(name) -> di)
          variants.foldLeft(newtenv){(currentTenv, wi) => wi.params.length match{
            case 0 => currentTenv + (wi.name -> ((AppT(name, tparams.map(VarT(_))), tparams.map(VarT(_))), false))
            case _ => currentTenv + (wi.name -> ((ArrowT(wi.params, AppT(name, tparams.map(VarT(_)))), tparams.map(VarT(_))), false))
          }
          }
        }
      }
    }

    def typeCheck(expr: Expr): Type = typeCheck(expr, Map())
  }

  object U {
    import Untyped._

    type Store = Map[Addr, Value]

    def malloc(sto: Store, env: Env): Addr = ((sto.keySet + 0) ++ env.values).max + 1

    def interp(expr: Expr, env: Env, sto: Store): (Value, Store) = expr match {
      case Id(name) => {
        if (env.contains(name)){
          val addr = env(name)
          if (sto.contains(addr)){
            sto(addr) match{
              case ExprV(ev, envv) => 
                val (ie, ienv) = interp(ev, envv, sto)
                (ie, ienv + (addr -> ie))
              case v => (v,sto)
            }
          }else{
            error("not in sto")
          }
        }else{
          error("not in env")
        }
      }

    case IntE(n) => (IntV(n), sto)
    case BooleanE(value) => (BooleanV(value), sto)
    case UnitE => (UnitV, sto)
    case Add(left, right) => interp(left, env, sto) match{
      case (IntV(n), nsto) => interp(right, env, nsto) match{
        case (IntV(m), msto) => (IntV(n + m), msto)
        case _ => error("not an integer")
      }
      case _ => error("not an integer")
    }

    case Mul(left, right) => interp(left, env, sto) match{
      case (IntV(n), nsto) => interp(right, env, nsto) match{
        case (IntV(m), msto) => (IntV(n * m), msto)
        case _ => error("not an integer")
      }
      case _ => error("not an integer")
    }

    case Div(left, right) => interp(left, env, sto) match{
      case (IntV(n), nsto) => interp(right, env, nsto) match{
        case (IntV(m), msto) => if (m == 0){
          error("zero")
        }else{
          (IntV(n / m), msto)          
        }
        case _ => error("not an integer")
      }
      case _ => error("not an integer")
    }

    case Mod(left, right) => interp(left, env, sto) match{
      case (IntV(n), nsto) => interp(right, env, nsto) match{
        case (IntV(m), msto) => if (m == 0){
          error("zero")
        }else{
          (IntV(n % m), msto)          
        }
        case _ => error("not an integer")
      }
      case _ => error("not an integer")
    }

    case Eq(left, right) => interp(left, env, sto) match{
      case (IntV(n), nsto) => interp(right, env, nsto) match{
        case (IntV(m), msto) => if (n == m){
          (BooleanV(true), msto)
        }else{
          (BooleanV(false), msto)
        }
        case _ => error("not an integer")
      }
      case _ => error("not an integer")
    }

    case Lt(left, right) => interp(left, env, sto) match{
      case (IntV(n), nsto) => interp(right, env, nsto) match{
        case (IntV(m), msto) => if (n < m){
          (BooleanV(true), msto)
        }else{
          (BooleanV(false), msto)
        }
        case _ => error("not an integer")
      }
      case _ => error("not an integer")
    }

    case Sequence(left, right) => {
      val (lv, ls) = interp(left, env, sto)
      interp(right, env, ls)
    }

    case If(cond, texpr, fexpr) => {
      val (cv, cs) = interp(cond, env, sto)
      cv match{
        case BooleanV(true) => interp(texpr, env, sto)
        case BooleanV(false) => interp(fexpr, env, sto)
        case _ => error("not a boolean")
      }
    }

    case Val(name, expr, body) => {
      val (ev, es) = interp(expr, env, sto)
      val addr = malloc(es, env)
      interp(body, env + (name -> addr), es + (addr -> ev))
    }

    case RecBinds(defs, b) =>{
      val emptyenv: Env = Map() 
      val menv = makeenv(defs, emptyenv, env, sto)
      val nenv = env ++ menv
      val nsto = makesto(defs, nenv, sto)
      interp(b, nenv, nsto)
    }

    case Fun(params, body) => (CloV(params, body, env), sto)

    case Assign(name, expr) => {
      if (env.contains(name)){
        val (ev, es) = interp(expr, env, sto)
        val addr = env(name)
        (UnitV, es + (addr -> ev))
      }else{
        error("not in env")
      }
    }

    case App(fun, args) => {
      val (fv, fs) = interp(fun, env, sto)
      val (argv, nsto) = processArgs(args, env, fs)
      fv match {
        case CloV(params, b, fenv) => if (params.length == args.length){
          val (renv, rsto) = makecor(params, argv, fenv, nsto)
          interp(b, renv, rsto)
        } else {
          error("length is different")
        }
        case ConstructorV(name) => (VariantV(name, argv), nsto)
        case _ => error("no appropriate matching")
      }
    }

    case Match(e, cases) =>{
      val (ev, es) = interp(e, env, sto)
      ev match {
        case VariantV(x, vals) =>
          if (cases.exists(_.variant == x)){
            cases.find(_.variant == x) match{
              case Some(tcase) =>{
                if(vals.length == tcase.names.length){
                  val (renv, rsto) = makecor(tcase.names, vals, env, es)
                  interp(tcase.body, renv, rsto)
                }else{
                  error("length is different")
                }   
              }
              case _ => error("error")
            }
          }else{
            error("no x")
          }
        case v => error("not variant")
      }
    }
    }
    def makeenv(defs: List[RecDef], emptyenv: Env, env: Env, sto: Store): Env = {
      defs.foldLeft(emptyenv) { (env2, recDef) =>
        val envi = recDef match {
          case Lazy(name, expr) =>
            val addr = malloc(sto, env2 ++ env)
            env + (name -> addr)
          case RecFun(name, params, body) =>
            val addr = malloc(sto, env2 ++ env)
            env + (name -> addr)
          case TypeDef(variants) =>
            variants.foldLeft(env) { (innerEnv, variant) =>
              val addr = malloc(sto, innerEnv ++  env2 ++ env)
              innerEnv + (variant.name -> addr)
            }
        }
        env2 ++ envi
      }
    }

    def makesto(defs: List[RecDef], env: Env, sto: Store): Store = {
      val emptysto: Store = Map()
      defs.foldLeft(sto) { (sto2, recDef) =>
        val stoi = recDef match{
          case Lazy(name, expr) =>
            emptysto + (env(name) -> ExprV(expr, env))
          case RecFun(name, params, body) =>
            emptysto + (env(name) -> CloV(params, body, env))
          case TypeDef(variants) =>
            variants.foldLeft(emptysto) { (innersto, variant) =>
              if (variant.empty){
                innersto + (env(variant.name) -> VariantV(variant.name, Nil)) 
              }else{
                innersto + (env(variant.name) -> ConstructorV(variant.name))
              }
            }
        }
        sto2 ++ stoi
      }
    }

    def processArgs(args : List[Expr], env: Env, fs: Store): (List[Value], Store) = {
      def helper(remainingArgs: List[Expr], evals: List[Value], astore: Store): (List[Value], Store) = {
        remainingArgs match{
          case Nil => (evals, astore)
          case e :: tail => 
            val (ev, es) = interp(e, env, astore)
            helper(tail, evals :+ ev, es)
        }
      }
      helper(args, List[Value](), fs)
    }

    def makecor(params: List[String], argv: List[Value], fenv: Env, stoN: Store): (Env, Store) = {
      def helper(remaining: List[(String, Value)], renv: Env, rsto: Store): (Env, Store) = {
        remaining match {
          case Nil => (renv, rsto)
          case (param, arg) :: tail =>
            val ai = ((rsto.keySet + 0) ++ renv.values).max + 1
            val newEnv = renv + (param -> ai)
            val newStore = rsto + (ai -> arg)
            helper(tail, newEnv, newStore)
        }
      }
      helper(params zip argv, fenv, stoN)
    }

    def interp(expr: Expr): Value = interp(expr, Map(), Map())._1
  }
}

