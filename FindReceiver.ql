/**
 * @name Exposure of Broadcast Receiver Component
 * @description Identifies both statically and dynamically registered broadcast receivers
 * @kind problem
 * @problem.severity warning
 * @security-severity 8.2
 * @precision high
 */

 import java
 import semmle.code.java.dataflow.DataFlow
 import semmle.code.xml.AndroidManifest
 import semmle.code.java.frameworks.android.Intent
 
 /** BroadcastReceiver Class */
 class BroadcastReceiverClass extends RefType {
     BroadcastReceiverClass() {
         this.getASupertype*().hasQualifiedName("android.content", "BroadcastReceiver")
     }
 }
 
 /** Holds if the receiver is statically registered in AndroidManifest.xml */
 predicate isStaticallyRegisteredReceiver(BroadcastReceiverClass receiver, AndroidReceiverXmlElement rec) {
     rec.getComponentName() = ["." + receiver.getName(), receiver.getQualifiedName()]
 }
 
 /** A method that registers a broadcast receiver dynamically */
 class RegisterReceiverMethod extends Method {
     RegisterReceiverMethod() {
         this.getDeclaringType().getASupertype*().hasQualifiedName("android.content", "Context") and
         this.hasName(["registerReceiver", "registerReceiverAsUser"])
     }
 }
 
 /** Holds if the receiver is dynamically registered in Code */
 predicate isDynamicallyRegisteredReceiver(BroadcastReceiverClass receiver, MethodAccess ma) {
     exists(RegisterReceiverMethod m |
         ma.getMethod() = m and
         (
             ma.getArgument(0).(ClassInstanceExpr).getConstructedType() = receiver
             or
             exists(Variable v |
                 v.getType() = receiver and ma.getArgument(0) = v.getAnAccess()
             )
         )
     )
 }
 
 from BroadcastReceiverClass receiver, string registrationType, string location
 where 
     (
         exists(AndroidReceiverXmlElement rec | 
             isStaticallyRegisteredReceiver(receiver, rec) and
             registrationType = "statically" and
             location = rec.getFile().getAbsolutePath()
         )
         or
         exists(MethodAccess ma |
             isDynamicallyRegisteredReceiver(receiver, ma) and
             registrationType = "dynamically" and
             location = ma.getFile().getAbsolutePath()
         )
     )
 select
     receiver.getQualifiedName(),
     registrationType,
     receiver.getPackage().getName(),
     "Registered " + registrationType + " at " + location
