import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.frameworks.android.Android

predicate isExplicitlyUnexported(AndroidComponent component) {
  exists(AndroidManifestXmlElement elem |
    elem = component.getAndroidManifestXmlElement() and
    elem.getAttribute("android:exported") = "false"
  )
}

predicate isDynamicallyRegisteredOrStarted(AndroidComponent component) {
  exists(MethodAccess ma |
    ma.getMethod().hasName([
      "registerReceiver", 
      "registerActivity", 
      "registerService", 
      "registerContentProvider",
      "startService",
      "bindService",
      "startActivity",
      "startActivityForResult"
    ]) and
    (
      ma.getAnArgument().getType() = component.getClass()
      or
      ma.getAnArgument().(VarAccess).getVariable().getType() = component.getClass()
    )
  )
}

predicate isIntentTarget(AndroidComponent component) {
  exists(ClassInstanceExpr newIntent |
    newIntent.getType() instanceof TypeIntent and
    newIntent.getAnArgument().getType() = component.getClass()
  )
}

predicate isUsedInPendingIntent(AndroidComponent component) {
  exists(MethodAccess ma |
    ma.getMethod().getDeclaringType() instanceof TypePendingIntent and
    ma.getAnArgument().getType() = component.getClass()
  )
}

from AndroidComponent component
where
  component.isExported()
  or
  (component.hasIntentFilter() and not isExplicitlyUnexported(component))
  or
  isDynamicallyRegisteredOrStarted(component)
  or
  component instanceof AndroidContentProvider
  or
  isIntentTarget(component)
  or
  isUsedInPendingIntent(component)
select component, 
  "This component is potentially exposed to external interactions. " +
  "Reason: " + 
  (if component.isExported()
    then "Explicitly exported in the manifest. "
   else "") +
  (if component.hasIntentFilter() and not isExplicitlyUnexported(component)
    then "Has an intent filter and not explicitly unexported. "
   else "") +
  (if isDynamicallyRegisteredOrStarted(component)
    then "Potentially dynamically registered or started. "
   else "") +
  (if component instanceof AndroidContentProvider
    then "Is a ContentProvider (potentially exposed by default in Android < 4.2). "
   else "") +
  (if isIntentTarget(component)
    then "Used as an Intent target. "
   else "") +
  (if isUsedInPendingIntent(component)
    then "Used in a PendingIntent. "
   else "") +
  "Verify if this exposure is intentional and properly secured."