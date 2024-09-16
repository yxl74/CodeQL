/**
 * @name Improper exposure of Broadcast Receiver Component
 * @description A broadcast receiver should be properly guarded
 * @kind problem
 * @problem.severity warning
 * @security-severity 8.2
 * @precision high
 */
import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.xml.AndroidManifest
import semmle.code.java.frameworks.android.Intent
/**BroadcastReceiver Class */
class BroadcastReceiverClass extends RefType{
   BroadcastReceiverClass(){
       this.getASupertype*().hasQualifiedName("android.content", "BroadcastReceiver")
   }
}
/**Holds if the receiver is statically registered in AndroidManifest.xml */
predicate isStaticallyRegisteredReceiver(BroadcastReceiverClass receiver, AndroidReceiverXmlElement rec){
   rec.getComponentName() = ["." + receiver.getName(), receiver.getQualifiedName()]
}
/**A method that registers a broadcast receiver dynamically */
class RegisterReceiverMethod extends Method{
   RegisterReceiverMethod() {
       this.getDeclaringType().getASupertype*().hasQualifiedName("android.content", "Context") and
       this.hasName(["registerReceiver", "registerReceiverAsUser"])
   }
}
/**Holds if the receiver is dynamically registered in Code */
predicate isDynamicallyRegisteredReceiver(BroadcastReceiverClass receiver){
   exists(MethodAccess ma, RegisterReceiverMethod m |
       ma.getArgument(0).(ClassInstanceExpr).getConstructedType() = receiver or
       exists(Variable v |
           v.getType() = receiver and ma.getArgument(0) = v.getAnAccess()
           )
       )
}
query predicate staticallyRegisteredReceivers(BroadcastReceiverClass receiver, string details){
   exists( AndroidReceiverXmlElement rec | isStaticallyRegisteredReceiver(receiver, rec)
   and
   details = "Statically registered in AndroidManifest.xml" )
}
from BroadcastReceiverClass receiver, AndroidReceiverXmlElement rec
where isStaticallyRegisteredReceiver(receiver, rec)
select
   receiver.getQualifiedName(),
   "statically",
   receiver.getPackage().getName()
