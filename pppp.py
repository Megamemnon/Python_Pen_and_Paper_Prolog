# Python Pen & Paper Prolog
# Copyright (c) 2022 Brian O'Dell 
# 
# 
# 

import sys
import enum

# globals
KB = []
Abort = False
varindex=0
CLICommand=False

class Termenum(enum.Enum):
  atom=1
  variable=2
  functor=3
  conjunction=4
  clause=5

def removeWhitespace(clause):
  clause=clause.replace(" ", "")
  clause=clause.replace("\t", "")
  clause=clause.replace("\n", "")
  return clause

def wff(clause):
  wffcl=removeWhitespace(clause)
  return wffcl

def importDatabase(filename):
  global KB
  f = open(filename, "r")
  lines = f.readlines()
  for l in lines:
    if l[0]!="\n" and l[0]!="%":
      wffcl = wff(l)
      if wffcl is not None:
        KB.append(wffcl)
      else:
        print("Syntax Error: {}".format(wffcl))

def printKB():
  global KB
  for kbentry in KB:
    print(kbentry)

def typeTerm(term):
  paren = 0
  comma = 0
  foundparen = 0
  priorx = ""
  for x in term:
    if x=="(":
      paren+=1
      foundparen=1
    if x==")":
      paren-=1
    if paren==0 and x==",":
      return Termenum.conjunction
    if paren==0 and priorx==":" and x=="-":
      return Termenum.clause
    priorx=x
  if foundparen:
    return Termenum.functor
  if term[0].isupper():
    return Termenum.variable
  return Termenum.atom

def getHead(clause):
  """returns head of clause (text prior to ":-") else returns clause"""
  impl = clause.find(":-")
  if impl!=-1:
    return clause[0:impl]
  return clause

def getBody(clause):
  """returns body of clause (text after ":-") else returns NONE"""
  impl = clause.find(":-")
  if impl!=-1:
    return clause[impl+2:]
  return None

def getOp(term):
  return term[:term.find("(")]

def getArgs(term):
  if term[-1]==".":
    term=term[:-1]
  term=term[term.find("(")+1:len(term)-1]
  return term

def getConjunctionList(clause):
  """returns a list of terms from provided clause"""
  clist=[]
  paren=0
  i=0
  j=0
  for x in clause:
    j+=1
    if x=="(":
      paren+=1
    if x==")":
      paren-=1
    if (x=="," or x==".") and paren==0:
      clist.append(clause[i:j-1])
      i=j
  if i!=j:
    clist.append(clause[i:])
  return clist

def indexVars(clause):
  global varindex
  varindex+=1
  return indexVarsR(clause)

def indexVarsR(term):
  global varindex
  t=typeTerm(term)
  if t==Termenum.clause:
    return indexVarsR(getHead(term))+":-"+indexVarsR(getBody(term))
  if t==Termenum.functor:
    return indexVarsR(getOp(term))+"("+indexVarsR(getArgs(term))+")"
  if t==Termenum.conjunction:
    cl=getConjunctionList(term)
    x=""
    for c in cl:
      x=x+indexVarsR(c)+","
    x=x[:-1]
    return x
  if t==Termenum.variable:
    if len(term)==1:
      return term+"_"+str(varindex)
    return term
  if t==Termenum.atom:
    return term
  return term

def substitute(clause, unifier):
  newclause=clause
  pnc=""
  while newclause!=pnc:
    pnc=newclause
    for u in unifier:
      if u!=[]:
        v=u.split("|")
        if len(v)==2:
          newclause=substituteR(newclause, v[0], v[1])
  return newclause

def substituteR(term,var,bound):
  t=typeTerm(term)
  if t==Termenum.clause:
    return substituteR(getHead(term), var, bound)+":-"+substituteR(getBody(term), var, bound)
  if t==Termenum.functor:
    return substituteR(getOp(term), var, bound)+"("+substituteR(getArgs(term), var, bound)+")"
  if t==Termenum.conjunction:
    cl=getConjunctionList(term)
    x=""
    for c in cl:
      x=x+substituteR(c, var, bound)+","
    x=x[:-1]
    return x
  if t==Termenum.variable:
    if term==var:
      return bound
    return term
  if t==Termenum.atom:
    return term
  return term

def containsVar(term):
  x=containsVarR(term)
  if x.find("$VAR$")!=-1:
    return True
  return False

def containsVarR(term):
  t=typeTerm(term)
  if t==Termenum.clause:
    return containsVarR(getHead(term))+":-"+containsVarR(getBody(term))
  if t==Termenum.functor:
    return containsVarR(getOp(term))+"("+containsVarR(getArgs(term))+")"
  if t==Termenum.conjunction:
    cl=getConjunctionList(term)
    x=""
    for c in cl:
      x=x+containsVarR(c)+","
    x=x[:-1]
    return x
  if t==Termenum.variable:
    return "$VAR$"
  if t==Termenum.atom:
    return term
  return term

def bind(var, term, unifier):
  unifier.append(var + "|" + term)

def getBound(var, unifier):
  if unifier is None:
    return None
  for u in unifier:
    us=u.split("|")
    if len(us)==2:
      if var==us[0]:
        return us[1]
  return None

def unify(term1, term2, unifier):
  """recursive unifification algorithm
  returns MGU ([var|term,... ])  
  or None upon failure"""
  if term1 is None or term2 is None or term1=="" or term2=="":
    return None
  if term1==term2:
    return unifier
  t1t=typeTerm(term1)
  t2t=typeTerm(term2)
  if t1t==Termenum.variable:
    return unifyVars(term1, term2, unifier)
  if t2t==Termenum.variable:
    return unifyVars(term2, term1, unifier)
  if t1t==Termenum.functor and t2t==Termenum.functor:
    op1=getOp(term1)
    op2=getOp(term2)
    uop=unify(op1, op2, unifier)
    if uop is None:
      return None
    args1=getArgs(term1)
    args2=getArgs(term2)
    uarg=unify(args1, args2, uop)
    if uarg is None:
      return None
    return compose(uop, uarg)
  if t1t==Termenum.conjunction and t2t==Termenum.conjunction:
    t1=getConjunctionList(term1)
    t2=getConjunctionList(term2)
    if len(t1)!=len(t2):
      return None
    i=len(t1)
    u=unifier.copy()
    for j in range(i):
      u2=unify(t1[j], t2[j], u)
      if u2 is None:
        return None
      u=compose(u, u2) 
    return u    
  return None

def unifyVars(var, term, unifier):
  x=getBound(var, unifier)
  if x is not None:
    return unify(x, term, unifier)
  if typeTerm(term)==Termenum.variable:
    x=getBound(term, unifier)
    if x is not None:
      return unifyVars(var, x, unifier)
  if unifier is None:
    u=[]
  else:
    u=unifier.copy()
  bind(var, term, u)
  return u

def compose(unifier1, unifier2):
  if unifier1 is None:
    if unifier2 is None:
      return []
    else:
      return unifier2
  elif unifier2 is None:
    return unifier1
  """applies unifier2 to unifier1 and appends unique unifier 2 bindings
  returns the resulting unifier"""
  newunifier=[]
  # populate newunifier by applying each binding in unifier2 
  # to the bound portion of bindings in unifier1
  for u in unifier1:
    if u!=[]:
      us=u.split("|")
      if len(us)==2:
        newunifier.append(us[0]+"|"+substitute(us[1], unifier2))
  nu=";".join(newunifier)
  # add bindings from unifier2 for variables 
  # not already present in newunifier to newunifier
  for u2 in unifier2:
    if u2!=[]:
      u2s=u2.split("|")
      if len(u2s)==2:
        found=0
        for nu in newunifier:
          if nu!=[]:
            nus=nu.split("|")
            if len(nus)==2:
              if u2s[0]==nus[0]:
                found=1
        if found==0:
          newunifier.append(u2)
  return newunifier

def resolve(goals, unifier, level):
  """recursive resolution algorithm
  includes a prompt with solutions and continuation
  returns the MGU"""
  global KB
  global Abort
  global CLICommand
  if Abort or goals is None:
    return None
  # TODO how to we get a clean/empty unifier/ans when we need to backtrack??
  ans=unifier # ans=[]
  # TODO Making a copy of KB probably isn't necessary unless my python is actually
  # modding strings in kb; but if it is necessary, perhaps we should pass it 
  # to the resolve function instead of creating a new copy each time resolve
  # is invoked
  workingKB = KB.copy()
  for r in goals:
    resolvent=r
    if resolvent[-1]==".":
      resolvent=resolvent[:-1]
    if unifier is not None:
      resolvent=substitute(resolvent, unifier) # or not
    for k in workingKB:
      br=False
      kbentry=k
      if kbentry[-1]==".":
        kbentry=kbentry[:-1]
      ikbentry = indexVars(kbentry)
      head = getHead(ikbentry)
      ans = unify(resolvent, head, unifier)
      if ans is not None:
        ans=compose(unifier, ans)
        # ??Why Not??
        ikbentry=substitute(ikbentry, ans)
        body = getBody(ikbentry)
        if body is not None:
          bodyTerms = getConjunctionList(body)
          for bt in bodyTerms:
            btt=[]
            btt.append(bt)
            ans = resolve(btt, ans, level+1)
            if Abort:
              return None
            if ans is None:
              br=True
        if level==1 and br==False:
          t=ikbentry
          tp=""
          while t!=tp:
            tp=t
            t=substitute(t, ans)
          if containsVar(t):
            br=True
          #   body=getBody(t)
          #   if body is not None:
          #     bodyTerms=getConjunctionList(body)
          #     for bt in bodyTerms:
          #       btt=[]
          #       btt.append(bt)
          #       ans=resolve(btt, ans, level+1)
          #       if Abort:
          #         return None
          #       if ans is None:
          #         br=True
          if br==False:
            # ans2=unify(t, kbentry, [])
            print("Yes")
            # print("Θ = {}".format(ans))
            # print("Θ2 = {}".format(ans2))
            # print("q = {}".format(ikbentry))
            if containsVar((goals[0])):
              x=unify(goals[0], getHead(t), [])
              print("Θ = {}".format(x))
            print("Θq = {}".format(t))
            if CLICommand:
              userinput="N"
            else:
              userinput=input("More? y/N ")
            if userinput[0]!="y" and userinput!="Y":
              Abort=1
              return None
        elif br==False:
          return ans
  return ans

def main():
  global Abort
  global CLICommand
  if len(sys.argv)>2:
    CLICommand=True
  if not CLICommand:
    print("Python Pen & Paper Prolog")
    print("Copyright (c) 2022 Brian O'Dell")
  if len(sys.argv)>1:
    importDatabase(sys.argv[1])  
  else:
    importDatabase("testkb")
  while 1:
    if CLICommand:
      userinput=sys.argv[2]
    else:
      userinput=input("]")
    userinput=removeWhitespace(userinput)
    if userinput=="quit." or userinput=="halt." or userinput=="exit.": 
      return
    if userinput=="list.":
      printKB()
    if userinput.find("?-")==0:
      userinput = userinput[2:]
      goals = []
      goals.append(userinput)
      Abort=False
      ans = resolve(goals, [], 1)
      if not CLICommand and ans is None:
        print("No.")
    if CLICommand:
      sys.exit(0)

# Main
if __name__ == "__main__":
  main()
