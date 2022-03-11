/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t S;   /* Operand stack of C0 values */
  ubyte *P;        /* Function body */
  size_t pc;       /* Program counter */
  c0_value *V;     /* The local variables */
};

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);
  
  /* Variables */
  c0v_stack_t S; 
  S = c0v_stack_new();
  ubyte *P;
  P = bc0->function_pool->code;
  int32_t *intpool = bc0->int_pool;
  char *stringpool = bc0->string_pool;
  size_t pc;
  pc = 0;
  c0_value *V;   /* Local variables (you won't need this till Task 2) */
  V = xcalloc(bc0->function_pool->num_vars, sizeof(c0_value));
  
  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack;
  callStack = stack_new();


  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    // fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
    //         P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      c0v_push(S,x);
      c0v_push(S,y);
      pc++;
      break;
    }



    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      if (stack_empty(callStack))
      {
        int retval = val2int(c0v_pop(S));
        assert(c0v_stack_empty(S));
        c0v_stack_free(S);
        free(V);
        stack_free(callStack,&free);
        IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", retval));
        return retval;
      }
      else{
        frame* tmp = pop(callStack);
        c0_value x = c0v_pop(S);
        c0v_stack_free(S);
        free(V);
        S = tmp->S;
        V = tmp->V;
        P = tmp->P;
        pc = tmp->pc;
        free (tmp);
        c0v_push(S,x);
        break;
      }
    }

// Another way to print only in DEBUG mode



    /* Arithmetic and Logical operations */

    case IADD:{
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      int sum = xpop+ypop;
      c0_value sumpush = int2val(sum);
      c0v_push(S,sumpush);
      pc++;
      break;
    }


    case ISUB:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      int sub = ypop-xpop;
      c0_value subpush = int2val(sub);
      c0v_push(S,subpush);
      pc++;
      break;
    }

    case IMUL:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      int mul = ypop*xpop;
      c0_value mulpush = int2val(mul);
      c0v_push(S,mulpush);
      pc++;
      break;
    }

    case IDIV:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      if (xpop==0) {c0_arith_error("divided by 0");}
      if (ypop==INT_MIN && xpop==-1){c0_arith_error("intmin divided by -1");}
      int div = ypop/xpop;
      c0_value divpush = int2val(div);
      c0v_push(S,divpush);
      pc++;
      break;
    }

    case IREM:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      if (xpop==0) {c0_arith_error("moded by 0");}
      if (ypop==INT_MIN && xpop==-1){c0_arith_error("intmin moded by -1");}
      int mod = ypop%xpop;
      c0_value modpush = int2val(mod);
      c0v_push(S,modpush);
      pc++;
      break;
    }

    case IAND:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      int and = ypop&xpop;
      c0_value andpush = int2val(and);
      c0v_push(S,andpush);
      pc++;
      break;
    }

    case IOR:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      int or = ypop|xpop;
      c0_value orpush = int2val(or);
      c0v_push(S,orpush);
      pc++;
      break;
    }
    case IXOR:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      int or = ypop^xpop;
      c0_value orpush = int2val(or);
      c0v_push(S,orpush);
      pc++;
      break;
    }
    case ISHR:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      if (xpop<0||xpop>31) {c0_arith_error("invalid shift");}
      int sr = ypop>>xpop;
      c0_value srpush = int2val(sr);
      c0v_push(S,srpush);
      pc++;
      break;
    }
    case ISHL:
    {
      c0_value x = c0v_pop(S);
      c0_value y = c0v_pop(S);
      int xpop = val2int(x);
      int ypop = val2int(y);
      if (xpop<0||xpop>31) {c0_arith_error("invalid shift");}
      int sl = ypop<<xpop;
      c0_value slpush = int2val(sl);
      c0v_push(S,slpush);
      pc++;
      break;
    }


    /* Pushing constants */

    case BIPUSH:
    {
      pc ++;
      int x = (int)(int8_t)P[pc];
      c0_value xpush = int2val(x);
      c0v_push(S,xpush);
      pc++;
      break;
    }

    case ILDC:
    {
      uint16_t c1 = (uint16_t)P[pc+1];
      uint16_t c2 = (uint16_t)P[pc+2];
      uint16_t c = (c1<<8)|c2;
      int result = intpool[c];
      c0_value resultpush = int2val(result);
      c0v_push(S,resultpush);
      pc += 3;
      break;

    }

    case ALDC:
    {
      uint16_t c1 = (uint16_t)P[pc+1];
      uint16_t c2 = (uint16_t)P[pc+2];
      uint16_t c = (c1<<8)|c2;
      char* result = &(stringpool[c]);
      c0_value resultpush = ptr2val((void*)result);
      c0v_push(S,resultpush);
      pc += 3;
      break;
    }

    case ACONST_NULL:
    {
      c0_value resultpush = ptr2val((void*)NULL);
      c0v_push(S,resultpush);
      pc += 1;
      break;
    }


    /* Operations on local variables */

    case VLOAD:
    {
      pc++;
      size_t i = (size_t)P[pc];
      c0v_push(S,V[i]);
      pc++;
      break;
    }
    case VSTORE:
    {
      pc++;
      c0_value x = c0v_pop(S);
      size_t i = (size_t)P[pc];
      V[i]=x;
      pc++;
      break;
    }


    /* Assertions and errors */

    case ATHROW:
    {
      c0_value x = c0v_pop(S);
      c0_user_error((char*)val2ptr(x));
      pc++;
      break;
    }

    case ASSERT:
    {
      c0_value ptr = c0v_pop(S);
      c0_value x = c0v_pop(S);
      int xres = val2int (x);
      if (xres == 0){c0_assertion_failure((char*)val2ptr(ptr));}
      pc++;
      break;


    }


    /* Control flow operations */

    case NOP:
    {
      pc++;
      break;
    }

    case IF_CMPEQ:
    {
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      if (val_equal(v1,v2)){
        uint16_t o1 = (uint16_t)P[pc+1];
        uint16_t o2 = (uint16_t)P[pc+2];
        pc += (int16_t)(o1<<8|o2);
        break;
      }
      pc+=3;
      break;


    }

    case IF_CMPNE:
    {
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      if (val_equal(v1,v2)==false){
        uint16_t o1 = (uint16_t)P[pc+1];
        uint16_t o2 = (uint16_t)P[pc+2];
        pc += (int16_t)(o1<<8|o2);
        break;
      }
      pc+=3;
      break;
      
    }

    case IF_ICMPLT:
    {
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      int y = val2int (v1);
      int x = val2int (v2);
      if (x<y){
        uint16_t o1 = (uint16_t)P[pc+1];
        uint16_t o2 = (uint16_t)P[pc+2];
        pc += (int16_t)(o1<<8|o2);
        break;
      }
      pc+=3;
      break;
    }

    case IF_ICMPGE:
    {
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      int y = val2int (v1);
      int x = val2int (v2);
      if (x>=y){
        uint16_t o1 = (uint16_t)P[pc+1];
        uint16_t o2 = (uint16_t)P[pc+2];
        pc += (int16_t)(o1<<8|o2);
        break;
      }
      pc+=3;
      break;
    }

    case IF_ICMPGT:
    {
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      int y = val2int (v1);
      int x = val2int (v2);
      if (x>y){
        uint16_t o1 = (uint16_t)P[pc+1];
        uint16_t o2 = (uint16_t)P[pc+2];
        pc += (int16_t)(o1<<8|o2);
        break;
      }
      pc+=3;
      break;
    }

    case IF_ICMPLE:
    {
      c0_value v1 = c0v_pop(S);
      c0_value v2 = c0v_pop(S);
      int y = val2int (v1);
      int x = val2int (v2);
      if (x<=y){
        uint16_t o1 = (uint16_t)P[pc+1];
        uint16_t o2 = (uint16_t)P[pc+2];
        pc += (int16_t)(o1<<8|o2);
        break;
      }
      pc+=3;
      break;
    }

    case GOTO:
    {
      uint16_t o1 = (uint16_t)P[pc+1];
      uint16_t o2 = (uint16_t)P[pc+2];
      pc += (int16_t)(o1<<8|o2);
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC:
    {
      uint8_t c1 = P[pc+1];
      uint8_t c2 = P[pc+2];
      struct function_info g = bc0->function_pool[c1<<8|c2];
      int n = g.num_args;
      c0_value* vg = xcalloc (sizeof (c0_value),g.num_vars);
      for (int i = 0; i < n; i++){
        c0_value tmp = c0v_pop(S);
        vg [n-i-1]=tmp;
      }
      frame* pause = xcalloc(sizeof(frame),1);
      pause->S = S;
      pause->P = P;
      pause->V = V;
      pause->pc = pc+3;
      push (callStack, (void*)pause);
      S = c0v_stack_new();
      P = g.code;
      pc = 0;
      V = vg;
      break;
    }

    case INVOKENATIVE:
    {
      uint8_t c1 = P[pc+1];
      uint8_t c2 = P[pc+2];
      struct native_info g = bc0 -> native_pool[c1<<8|c2];
      int n = g.num_args;
      c0_value* vg = xcalloc (sizeof (c0_value),n);
      for (int i = 0; i < n; i++){  
        c0_value tmp = c0v_pop(S);
        vg [n-i-1]=tmp;
      }
      uint16_t index = g.function_table_index;
      native_fn* function = native_function_table[index];
      c0_value result = (*function)(vg);
      c0v_push (S,result);
      pc+=3;
      free(vg);
      break;

    }


    /* Memory allocation and access operations: */

    case NEW:
    {
      uint8_t s = P[pc+1];
      pc += 2;
      char* a = xcalloc(sizeof(char),s);
      c0_value result = ptr2val((void*)a);
      c0v_push(S,result);
      break;
    }

    case IMLOAD:
    {
      void* popped  = val2ptr(c0v_pop(S));
      if (popped != NULL){
        int32_t x = *(int*)(popped);
        c0_value xpush = int2val (x);
        c0v_push (S,xpush);
      }
      else{
        c0_memory_error("null pointer");
      }
      pc++;
      break;
    }



    case IMSTORE:
    {
      int intpopped = val2int(c0v_pop(S));
      void* addresspopped = val2ptr(c0v_pop(S));
      if(addresspopped != NULL){
        *(int*)(addresspopped) = intpopped;
      }
      else{
        c0_memory_error("null pointer");
      }
      pc++;
      break;
    }

    case AMLOAD:
    {
      void* popped  = val2ptr(c0v_pop(S));
      if (popped != NULL){
        void* x = *(void**)(popped);
        c0_value xpush = ptr2val (x);
        c0v_push (S,xpush);
      }
      else{
        c0_memory_error("null pointer");
      }
      pc++;
      break;
    }

    case AMSTORE:
    {
      void* b = val2ptr(c0v_pop(S));
      void* a = val2ptr(c0v_pop(S));
      if (a!=NULL){
        *(void**)a = b;
      }
      else{
        c0_memory_error("null pointer");
      }
      pc++;
      break;


    }

    case CMLOAD:
    {
      void* popped  = val2ptr(c0v_pop(S));
      if (popped != NULL){
        int32_t x = (int)(*(char*)(popped));
        c0_value xpush = int2val (x);
        c0v_push (S,xpush);
      }
      else{
        c0_memory_error("null pointer");
      }
      pc++;
      break;
    }   

    case CMSTORE:
    {
      int popped = val2int(c0v_pop(S));
      void* addresspopped = val2ptr(c0v_pop(S));
      if(addresspopped != NULL){
        *(char*)(addresspopped) = (char)(popped&0x7f);
      }
      else{
        c0_memory_error("null pointer");
      }
      pc++;
      break;
    }


    case AADDF:
    {
      uint8_t f = P[pc+1];
      char* popped  = (char*)val2ptr(c0v_pop(S));
      if (popped != NULL){
        popped = popped+f;
        c0v_push(S,ptr2val((void*)popped));
      }
      else{
        c0_memory_error("null pointer");
      }
      pc+=2;
      break;
    }   


    /* Array operations: */

    case NEWARRAY:
    {
      uint8_t s = P[pc+1];
      pc += 2;
      int n = val2int(c0v_pop(S));
      c0_array* new = xcalloc(sizeof(c0_array),1);
      if (n>0){
        char* a = xcalloc(sizeof(char)*s,n);
        new->elems= (void*)a;
        new->count= n;
        new->elt_size = s;
      }
      else if (n==0){
        new->elems= NULL;
        new->count= n;
        new->elt_size = s;
      }
      else{
        c0_memory_error("negative length");
      }
      c0_value result = ptr2val((void*)new);
      c0v_push(S,result);
      break;
    }


    case ARRAYLENGTH:
    {
      void* popped  = val2ptr(c0v_pop(S));
      if (popped != NULL){
        c0_array* array = (c0_array*)popped;
        int length = array->count;
        c0v_push(S,int2val(length));
        
      }
      else{
        c0_memory_error("null pointer");
      }
      pc++;
      break;
    }   


    case AADDS:
    {
      int i = val2int(c0v_pop(S));
    
      void* popped  = val2ptr(c0v_pop(S));
      if (popped != NULL){
        c0_array* array = (c0_array*)popped;
        if (i>=array->count || i<0)
        {
          c0_memory_error("invalid move");
        }
       
        char* elems = (char*)array->elems;
        int s = array->elt_size;
        elems += s*i;
        c0v_push(S,ptr2val ((void*)elems));
        
      }
      else{
        c0_memory_error("null pointer");
      }
      pc++;
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
