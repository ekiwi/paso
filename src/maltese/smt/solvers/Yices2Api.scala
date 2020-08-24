/*
 * Copyright (c) 2019, Kevin Laeufer <laeufer@cs.berkeley.edu>
 *
 * This file is dual licensed under 3-Clause BSD and GPLv3 License (to be compatible with Yices2).
 */

package maltese.smt.solvers


import com.sun.jna.{Library, Native, NativeLibrary, Pointer}
import com.sun.jna.ptr.{IntByReference, LongByReference}

trait Yices2Api extends Library {
  // needs to be called first
  def yices_init(): Unit
  // releases all data
  def yices_exit(): Unit
  // resets terms etc.
  def yices_reset(): Unit

  def yices_is_thread_safe(): Int

  ///////////////////////
  // Error
  //////////////////////
  type ErrorCodeT = Yices2Api.ErrorCodeT
  def yices_error_code(): ErrorCodeT
  def yices_error_string(): String
  def yices_free_string(s: String): Unit // call to release string from yices_error_string


  ///////////////////////
  // Types
  //////////////////////
  type TypeT = Yices2Api.TypeT
  def yices_bool_type(): TypeT
  def yices_bv_type(size: Int): TypeT
  def yices_new_uninterpreted_type(): TypeT
  def yices_function_type(n: Int, domains: Array[TypeT], range: TypeT): TypeT

  ///////////////////////
  // Terms
  //////////////////////
  type TermT = Yices2Api.TermT

  // arrays are modelled as functions with the update function
  def yices_application(fun: TermT, n: Int, args: Array[TermT]): TermT
  def yices_update(fun: TermT, n: Int, args: Array[TermT], newValue: TermT): TermT
  def yices_lambda(n: Int, args: Array[TermT], body: TermT): TermT

  //
  def yices_constant(tpe: TypeT, index: Int): TermT
  def yices_new_uninterpreted_term(tpe: TypeT): TermT
  def yices_new_variable(tpe: TypeT): TermT

  // bool
  def yices_true(): TermT
  def yices_false(): TermT
  def yices_not(arg: TermT): TermT
  def yices_or(n: Int, arg: Array[TermT]): TermT
  def yices_or2(t1: TermT, t2: TermT): TermT
  def yices_and(n: Int, arg: Array[TermT]): TermT
  def yices_and2(t1: TermT, t2: TermT): TermT
  def yices_xor(n: Int, arg: Array[TermT]): TermT
  def yices_xor2(t1: TermT, t2: TermT): TermT
  def yices_iff(t1: TermT, t2: TermT): TermT
  def yices_implies(t1: TermT, t2: TermT): TermT

  // mixed
  def yices_ite(cond: TermT, then_term: TermT, else_term: TermT): TermT
  def yices_eq(t1: TermT, t2: TermT): TermT
  def yices_neq(t1: TermT, t2: TermT): TermT
  def yices_distinct(n: Int, arg: Array[TermT]): TermT

  // bit vector
  def yices_bvconst_int32(bits: Int, value: Int): TermT
  def yices_bvconst_int64(bits: Int, value: Long): TermT
  def yices_parse_bvbin(s: String): TermT

  // bv arithmetic
  def yices_bvadd(t1: TermT, t2: TermT): TermT
  def yices_bvsub(t1: TermT, t2: TermT): TermT
  def yices_bvneg(t1: TermT): TermT
  def yices_bvmul(t1: TermT, t2: TermT): TermT
  //def yices_bvsquare(t1: TermT, t2: TermT): TermT
  //def yices_bvpower(t1: TermT, d: Int): TermT
  def yices_bvdiv(t1: TermT, t2: TermT): TermT
  def yices_bvrem(t1: TermT, t2: TermT): TermT
  def yices_bvsdiv(t1: TermT, t2: TermT): TermT
  def yices_bvsrem(t1: TermT, t2: TermT): TermT
  def yices_bvsmod(t1: TermT, t2: TermT): TermT

  // bv bitwise
  def yices_bvnot(t: TermT): TermT
  def yices_bvnand(t1: TermT, t2: TermT): TermT
  def yices_bvnor(t1: TermT, t2: TermT): TermT
  def yices_bvnxor(t1: TermT, t2: TermT): TermT
  def yices_bvshl(t1: TermT, t2: TermT): TermT
  def yices_bvlshr(t1: TermT, t2: TermT): TermT
  def yices_bvashr(t1: TermT, t2: TermT): TermT
  def yices_bvor(n: Int, arg: Array[TermT]): TermT
  def yices_bvor2(t1: TermT, t2: TermT): TermT
  def yices_bvand(n: Int, arg: Array[TermT]): TermT
  def yices_bvand2(t1: TermT, t2: TermT): TermT
  def yices_bvxor(n: Int, arg: Array[TermT]): TermT
  def yices_bvxor2(t1: TermT, t2: TermT): TermT

  // bv constant shifts
  def yices_shift_left0(t: TermT, n: Int): TermT
  def yices_shift_right0(t: TermT, n: Int): TermT
  def yices_ashift_right(t: TermT, n: Int): TermT


  // bv other
  def yices_bvextract(t: TermT, lsb: Int, msb: Int): TermT
  def yices_bvconcat2(t1: TermT, t2: TermT): TermT
  def yices_bvconcat(n: Int, arg: Array[TermT]): TermT
  def yices_sign_extend(t: TermT, n: Int): TermT
  def yices_zero_extend(t: TermT, n: Int): TermT

  // bv reduction (all return bv<1>)
  def yices_redand(t: TermT): TermT
  def yices_redor(t: TermT): TermT

  // bv comparisons
  def yices_bveq_atom(t1: TermT, t2: TermT): TermT
  def yices_bvneq_atom(t1: TermT, t2: TermT): TermT
  def yices_bvge_atom(t1: TermT, t2: TermT): TermT
  def yices_bvgt_atom(t1: TermT, t2: TermT): TermT
  def yices_bvle_atom(t1: TermT, t2: TermT): TermT
  def yices_bvlt_atom(t1: TermT, t2: TermT): TermT
  def yices_bvsge_atom(t1: TermT, t2: TermT): TermT
  def yices_bvsgt_atom(t1: TermT, t2: TermT): TermT
  def yices_bvsle_atom(t1: TermT, t2: TermT): TermT
  def yices_bvslt_atom(t1: TermT, t2: TermT): TermT

  ///////////////////////
  // Solver Config
  //////////////////////
  type ConfigT = Yices2Api.ConfigT
  def yices_new_config(): ConfigT
  def yices_default_config_for_logic(config: ConfigT, logic: String): Int

  ///////////////////////
  // Solver Context
  //////////////////////
  type ContextT = Yices2Api.ContextT

  type SmtStatusT = Yices2Api.SmtStatusT
  type ParamsT = Yices2Api.ParamsT
  def yices_new_context(config: ConfigT): ContextT
  def yices_free_context(ctx: ContextT): Unit
  def yices_reset_context(ctx: ContextT): Unit
  def yices_push(ctx: ContextT): Int  // 0 on success
  def yices_pop(ctx: ContextT): Int   // 0 on success
  def yices_assert_formula(ctx: ContextT, formula: TermT): Int // 0 on success
  def yices_check_context(ctx: ContextT, params: ParamsT): SmtStatusT
  def yices_check_context_with_assumptions(ctx: ContextT, params: ParamsT, n: Int, terms: Array[TermT]): SmtStatusT

  ///////////////////////
  // Params
  //////////////////////
  def yices_new_param_record(): ParamsT
  def yices_set_param(params: ParamsT, name: String, value: String): Int // 0 on success
  def yices_free_param_record(params: ParamsT): Unit

  ///////////////////////
  // Model
  //////////////////////
  type ModelT = Yices2Api.ModelT
  def yices_get_model(ctx: ContextT, keepEliminated: Int): ModelT
  def yices_free_model(model: ModelT): Unit
  def yices_get_bool_value(model: ModelT, term: TermT, value: IntByReference): Int
  // for integer terms
  def yices_get_int32_value(model: ModelT, term: TermT, value: IntByReference): Int
  def yices_get_int64_value(model: ModelT, term: TermT, value: LongByReference): Int
  // for bitevector terms, Array[Int] needs to be at least N-bits long
  def yices_get_bv_value(model: ModelT, term: TermT, value: Array[Int]): Int
}

object Yices2Api {
  case class Info(Version: String, BuildArch: String, BuildMode: String, BuildDate: String)
  def getInfo(): Info = {
    val lib = NativeLibrary.getInstance("yices")
    def read(name: String) = lib.getGlobalVariableAddress(name).getPointer(0).getString(0)
    val info = Info(
      Version = read("yices_version"),
      BuildArch = read("yices_build_arch"),
      BuildMode = read("yices_build_mode"),
      BuildDate = read("yices_build_date")
    )
    lib.dispose()
    info
  }

  // error code
  type ErrorCodeT = Int // typedef enum (tices_types.h:299)
  val NO_ERROR: Int = 0

  type TypeT = Int
  type TermT = Int
  type ConfigT = Pointer
  type ContextT = Pointer
  type ParamsT = Pointer
  type ModelT = Pointer

  // status_t
  type SmtStatusT = Int // enum
  val STATUS_IDLE: Int = 0
  val STATUS_SEARCHING: Int = 1
  val STATUS_UNKNOWN: Int = 2
  val STATUS_SAT: Int = 3
  val STATUS_UNSAT: Int = 4
  val STATUS_INTERRUPTED: Int = 5
  val STATUS_ERROR: Int = 6

  // convenience functions
  def assertNoError(yices_lib: Yices2Api = lib): Unit = {
    val error_no = yices_lib.yices_error_code()
    if(error_no != NO_ERROR) {
      val error_str = yices_lib.yices_error_string()
      val error = new String(error_str)
      yices_lib.yices_free_string(error_str)
      throw new RuntimeException(s"Call to yices2 failed with error: $error")
    }
  }


  def load(): Yices2Api = {
    val yices_lib = Native.load("yices", classOf[Yices2Api])
    yices_lib.yices_init() ; assertNoError(yices_lib)
    yices_lib
  }

  def exit(): Unit = maybeLib match {
    case Some(lib) => {
      lib.yices_exit() ; assertNoError()
      maybeLib = None
    }
    case None => None
  }

  private var maybeLib: Option[Yices2Api] = None

  def lib: Yices2Api = maybeLib match {
    case Some(lib) => lib
    case None => val lib = load(); maybeLib = Some(lib) ; lib
  }
}
