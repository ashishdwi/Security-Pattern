module Security_Patterns
open util/ordering[SecurityPatterns] as SP
enum AccessScheme {allow, deny}
enum Rules {valid, Invalid}
sig Resource { } 
sig Account { }  
abstract sig State {}
one sig WaitForAuth, Idle, Authenticated, Busy, Reset extends State {}
abstract sig Operation { } 
sig Fundtransfer, CheckService, BillPayment, Request, CheckAuth, Login, RESET extends Operation { }

sig SecurityPatterns { state : one State, op : Operation }

pred reqSSO [sp, sp' : SecurityPatterns] { sp.state = Idle && sp'.op=Login && sp'.state = WaitForAuth }

pred checkAuth [sp, sp' : SecurityPatterns] {sp.state=WaitForAuth && sp'.op=CheckAuth 
&& sp'.state=Authenticated}

pred reqResource [sp, sp' : SecurityPatterns] { sp.state=Authenticated && 
sp'.op= Request && sp'.state=Idle }

pred useResource [sp, sp' : SecurityPatterns] { sp.state=Idle && 
sp'.op= (Fundtransfer + CheckService + BillPayment) && sp'.state=Busy }

pred reset [sp, sp' : SecurityPatterns ] { sp.state = Busy && sp'.state= Reset}

pred init [sp : SecurityPatterns ] { sp.state = Idle }

pred traces { init [SP/ first [] ] && all sp:SecurityPatterns-SP/last[] | let sp' = SP/next[sp] |
((reqSSO[sp, sp'] && sp'.op=Login) or (checkAuth[sp, sp'] && sp'.op=CheckAuth) or
(reqResource[sp, sp'] && sp'.op=Request) or (useResource[sp, sp'] && 
sp'.op=(Fundtransfer + CheckService + BillPayment)) or (reset [sp, sp'] && sp'.op=RESET) ) }

pred perfTrans { traces &&  (SP/last[]).op=RESET && RESET ! in (SecurityPatterns - SP/last[]).op}

//run perfTrans for 6

sig USER { sso : SingleSignOn} { all s : SingleSignOn |
               s in sso implies s.user = this && s.has = CheckPoint && s.user = USER}

sig SingleSignOn extends SecurityPatterns {  has : one CheckPoint, user : USER  } 

sig CheckPoint extends SecurityPatterns {  accessType : AccessScheme, checkk : Authenticator ->  Policy } {  all a : Authenticator | 
   all p : Policy | a.auth = USER && p.enforce = Rules && (a.cp.accessType=allow implies p.enforce=valid) }

sig Authenticator extends SecurityPatterns {  accessType : AccessScheme,  auth : set USER, cp : CheckPoint  } 

sig Policy extends SecurityPatterns {  accessType : AccessScheme, enforce :set Rules, cp : CheckPoint  } 

sig SecureProxy extends SecurityPatterns { accessType : AccessScheme, make : Account -> Operation } 

pred supported [acct : Account, op : Operation]  {
 acct  ->  op  in SecureProxy.make               } 
pred authPolicy[p : Policy, a : Authenticator]
            {  a -> p in CheckPoint.checkk  }
pred unauthPolicy[p : Policy, a : Authenticator]
            {  a -> p not in CheckPoint.checkk  }
pred authenticated [acct : Account, user : USER, op : Operation]  {
          all p : Policy | all a : Authenticator| supported [acct, op] 
                                && user= Authenticator.auth && authPolicy[p, a]  } 
pred unauthenticated [acct : Account, user : USER, op : Operation]  {
            all p : Policy | all a : Authenticator| unauthPolicy[p, a] && supported [acct, op] 
                                && user != Authenticator.auth      }
pred performed [acct : Account, user : USER, op : Operation]  {
           supported [acct, op] && authenticated[acct, user, op]
}
pred noPerformed [acct : Account, user : USER, op : Operation]  {
           supported [acct, op] && authenticated[acct, user, op]
}
assert Operation_Performed
{ all a : Authenticator | all sso : SingleSignOn | all acct : Account | all op : Operation |
all user : USER | all p : Policy | all sp, sp' : SecurityPatterns | a.auth = user &&
                    p.enforce = valid && useResource [sp, sp']
                    && sso.has.accessType = allow && supported[acct, op] => performed[acct, user, op] }
fact { all acct : Account | all op : Operation | all user : USER | 
        supported[acct, op] && authenticated[acct, user, op] => performed[acct, user, op] }
fact { some acct : Account | some op : Operation | some user : USER |
  supported[acct, op] && unauthenticated[acct, user, op] => noPerformed[acct, user, op] }

run unauthenticated for 3