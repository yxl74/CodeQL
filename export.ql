import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.frameworks.android.Android
import semmle.code.xml.AndroidManifest

predicate isExplicitlyUnexported(AndroidComponent component) {
  exists(AndroidComponentXmlElement elem |
    elem.getComponent() = component and
    elem.getAttributeValue("android:exported") = "false"
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
      ma.getAnArgument().getType() = component.getType()
      or
      ma.getAnArgument().(VarAccess).getVariable().getType() = component.getType()
    )
  )
}

predicate isIntentTarget(AndroidComponent component) {
  exists(ClassInstanceExpr newIntent |
    newIntent.getConstructedType() instanceof TypeIntent and
    newIntent.getAnArgument().getType() = component.getType()
  )
}

predicate isUsedInPendingIntent(AndroidComponent component) {
  exists(MethodAccess ma |
    ma.getMethod().getDeclaringType() instanceof TypePendingIntent and
    ma.getAnArgument().getType() = component.getType()
  )
}

predicate isExported(AndroidComponent component) {
  exists(AndroidComponentXmlElement elem |
    elem.getComponent() = component and
    (
      elem.getAttributeValue("android:exported") = "true"
      or
      not exists(elem.getAttributeValue("android:exported")) and
      exists(IntentFilterXmlElement filter | filter.getParent() = elem)
    )
  )
}

from AndroidComponent component
where
  isExported(component)
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
  (if isExported(component)
    then "Explicitly exported in the manifest or has an intent filter without android:exported=\"false\". "
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