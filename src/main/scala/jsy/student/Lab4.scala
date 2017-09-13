package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <D'Artagnan Wake>
   * 
   * Partner: <Juan>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => {
      if (h1 == h2) compressRec(t1)
      else h1 :: compressRec(t1)
    }
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match {
      case Nil => h :: acc
      case h1 :: t => if (h == h1) acc else h :: acc
    }
  }
  
  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match {
    case Some(x) => x :: t
    case None => h :: mapFirst(t)(f)
    }
  }
  
  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => loop(f(loop(acc, l), d), r)
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, acc) = foldLeft(t)((true, None: Option[Int])){
      (acc, h) => acc match {
        case (_, None) => (true, Some(h))
        case (v, Some(x)) => if(h <= x) (false, Some(x)) else (v, Some(x))
      }
    }
    b
  }

  /* Type Inference */

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => lookup(env, x)
      case Decl(mode, x, e1, e2) => typeof(extend(env, x, typeof(env, e1)), e2)
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (TNumber, tgot) => err(tgot, e2)
        case (TString, tgot) => err(tgot, e2)
        case (tgot, TNumber) => err(tgot, e1)
        case (tgot, TString) => err(tgot, e1)
      }
      case Binary(Minus | Times | Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TNumber, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(Eq | Ne, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        //1
        case (TFunction(_, _), _) => err(typeof(env, e1), e1)
        case (_, TFunction(_, _)) => err(typeof(env, e2), e2)
        case (t1, t2) if t1 == t2 => t1
        case (tgot1, tgot2) => err(tgot1, e1)
      }
      case Binary(Lt | Le | Gt | Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (TNumber, tgot) => err(tgot, e2)
        case (TString, tgot) => err(tgot, e2)
        case (tgot, TNumber) => err(tgot, e1)
        case (tgot, TString) => err(tgot, e1)
      }
      case Binary(And | Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (TBool, tgot) => err(tgot, e2)
        case (tgot, TBool) => err(tgot, e1)
      }
      case Binary(Seq, e1, e2) => typeof(env, e1); typeof(env, e2)
      case If(e1, e2, e3) => typeof(env, e1) match {
        //1
        case TBool => {
          if (typeof(env, e2) == typeof(env, e3)) typeof(env, e2) else err(typeof(env, e3), e3)
        }
        case tgot => err(tgot, e1)
      }


      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        def f(envi: TEnv, parami: (String, MTyp)): TEnv = parami match {
          case (xi, MTyp(_, ti)) => extend(envi, xi, ti)
        }

        val env1 = (p, tann) match {
          /** *** Add cases here *****/
          case (None, None) => env
          case (None, Some(x)) => env
          case (Some(x), Some(t)) => extend(env, x, t)
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1)(f)

        // Infer the type of the function body
        val t = typeof(env2, e1)
        // Check with the possibly annotated return type
        tann match {
          case None => TFunction(params, t)
          case Some(x) => if (x == t) TFunction(params, t) else err(TUndefined, e1)
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach { tup =>
            val (t1, t2) = tup
            t1 match {
              case (s, MTyp(_, t)) => if (t == typeof(env, t2)) typeof(env, t2) else err(TUndefined, t2)
            }
          }
          tret
        case tgot => err(tgot, e1)
      }

      case Obj(fields) => TObj(fields.map((e) => (e._1, typeof(env, e._2)))) //TObj(fields.mapValues(e1 => typeof(env, e1)))
      /*case GetField(e1, f) => typeof(env, e1) match {
        case TObj(fields) => lookup(fields, f)
        case tgot => err(tgot, e1)
      }*/
      case GetField(e1, f) => typeof(env, e1) match {
        case TObj(fields) if fields.contains(f) => fields(f)
        case tgot => err(tgot, e1)
      }
    }
  }
  
  
  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => if (s1 < s2) true else false
        case Le => if (s1 <= s2) true else false
        case Gt => if (s1 > s2) true else false
        case Ge => if (s1 >= s2) true else false
      }

      case (N(v1), N(v2)) => bop match {
        case Lt => if (v1 < v2) true else false
        case Le => if (v1 <= v2) true else false
        case Gt => if (v1 > v2) true else false
        case Ge => if (v1 >= v2) true else false
      }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(e) => loop(e, n + 1)
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, esub, x))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (y == x) esub else e
      case Decl(mode, y, e1, e2) => if(x == y) Decl(mode, y,subst(e1), e2) else Decl(mode, y, subst(e1), subst(e2))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => p match {
        case None => {
          val sub1 = params.foldLeft(true)((acc, y) => if (x == y._1) acc && false else acc && true)
          if(sub1)
            Function(p, params, tann, subst(e1))
          else
            Function(p, params, tann, e1)
        }
        case Some(f) => {
          val sub2 = params.foldLeft(true)((acc, y) => if (x == y._1) acc && false else acc && true)
          if(x == f || sub2 == false)
            Function(p, params, tann, e1)
          else
            Function(p, params, tann, subst(e1))
        }
      }
      case Call(e1, args) => Call(subst(e1), args.map((y) => subst(y)))
        /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.mapValues(v => subst(v)))
      case GetField(e1, f) => if( x!= f) GetField(subst(e1), f) else e
    }

    val fvs = freeVars(esub)
    def fresh(x: String): String = if (fvs contains(x)) fresh(x + "$") else x
    subst(e)
  }

  /* Rename bound variables in e */
  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => Unary(uop, ren(env, e1))
        case Binary(bop, e1, e2) => Binary(bop, ren(env, e1), ren(env, e2))
        case If(e1, e2, e3) => If(ren(env,e1), ren(env, e2), ren(env, e3))

        case Var(y)  => {
          if(env.contains(y))
            Var(lookup(env,y))
          else
            Var(y)
        }
        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          Decl(mode, yp, e1, ren(env, e2))

        case Function(p, params, retty, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => (p, env)
            case Some(x) => {
              val newName = fresh(x)
              (Some(newName),extend(env, x, newName))
            }
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            (h, acc) => {
              val rename = (fresh(h._1), h._2)
              (rename :: acc._1 ,extend(acc._2, h._1, fresh(h._1)))
            }
          }
          Function(pp, paramsp, retty, ren(envpp, e1))
        }

        case Call(e1, args) => Call(ren(env, e1), args.map((x) => ren(env,x)))

        case Obj(fields) => Obj(fields.map( e => (fresh(e._1), ren(extend(env, e._1, fresh(e._1)), e._2))))
        case GetField(e1, f) => GetField(ren(env, e1), f)
      }
    }
    ren(empty, e)
  }


  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => !isValue(e)
    case MName => false
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, N(n)) => N(-n)

      case Unary(Not, B(b)) => B(!b)

      case Binary(Seq, v1, e1) if isValue(v1) => e1

      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)

      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)

      case Binary(Lt, N(n1), N(n2)) => B(n1 < n2)
      case Binary(Lt, S(s1), S(s2)) => B(s1 < s2)

      case Binary(Le, N(n1), N(n2)) => B(n1 <= n2)
      case Binary(Le, S(s1), S(s2)) => B(s1 <= s2)

      case Binary(Gt, N(n1), N(n2)) => B(n1 > n2)
      case Binary(Gt, S(s1), S(s2)) => B(s1 > s2)

      case Binary(Ge, N(n1), N(n2)) => B(n1 >= n2)
      case Binary(Ge, S(s1), S(s2)) => B(s1 >= s2)

      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)

      case Binary(And, B(b), e1) => b match {
        case true => e1
        case false => B(false)
      }

      case Binary(Or, B(b), e1) => b match {
        case true => B(true)
        case false => e1
      }

      case If(B(b), e2, e3) => b match {
        case true => e2
        case false => e3
      }
      case Decl(mode, y, e1, e2) if (!isRedex(mode, e1)) => substitute(e2, e1, y)


      /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip.forall(e => !isRedex(e._1._2.m, e._2))) {
              val e1p = pazip.foldRight(e1) {
                (l, acc) => {
                  val (par, arg) = l    // ((string, MTyp), Expr)
                  substitute(acc, arg, par._1)    //l._2 replace arg
                }
              }
              p match {
                case None => e1p
                case Some(x1) => substitute(e1p, v1, x1)
              }
            }
            else {
              val pazipp = mapFirst(pazip) {
                e => if(!isRedex(e._1._2.m, e._2)) None else Some((e._1, step(e._2)))
              }
              Call(v1, pazipp.map(e => e._2))
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */

      case GetField(Obj(fields), f) if fields.forall(e => isValue(e._2)) => fields(f)




      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      case Binary(bop, v1, e1) if(isValue(v1)) => Binary(bop, v1, step(e1))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      //SearchUnary//
      case Unary(uop, e1) => Unary(uop, step(e1))

      //SearchIf//
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      //SearchConst//
      case Decl(mode,y, e1, e2) if(isRedex(mode, e1)) => Decl(mode, y, step(e1), e2)


        /***** More cases here */
        /***** Cases needing adapting from Lab 3 */
      case Call(e1, args) => Call(step(e1), args)

      case Obj(fields) => Obj(fields.mapValues(e => if(isValue(e)) e else step(e)))
      case GetField(e1, f) => GetField(step(e1), f)
      /*case Obj(fields) => {
        val newField: Map[String,Expr] = Map()
        val newObj = fields.foldLeft((true, newField)) {
          case ((kg, accField), (f, e)) =>
            if(kg)
              if(isValue(e)) (kg, accField + (f -> e))
              else (false, accField + (f -> step(e)))
            else
              (false, accField + (f -> e)) // is this right?
        }
        Obj(newObj._2)
        }*/



        /***** New cases for Lab 4. */

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}

