import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.frameworks.android.Android
import semmle.code.xml.AndroidManifest

class AndroidComponent extends Class {
  AndroidComponent() {
    this.getASupertype*().hasQualifiedName("android.app", [
      "Activity",
      "Service",
      "BroadcastReceiver",
      "ContentProvider"
    ])
  }
}

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
      ma.getAnArgument().getType() = component
      or
      ma.getAnArgument().(VarAccess).getVariable().getType() = component
    )
  )
}

predicate isIntentTarget(AndroidComponent component) {
  exists(ClassInstanceExpr newIntent |
    newIntent.getConstructedType().hasQualifiedName("android.content", "Intent") and
    newIntent.getAnArgument().getType() = component
  )
}

predicate isUsedInPendingIntent(AndroidComponent component) {
  exists(MethodAccess ma |
    ma.getMethod().getDeclaringType().hasQualifiedName("android.app", "PendingIntent") and
    ma.getAnArgument().getType() = component
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
  component.getASupertype*().hasQualifiedName("android.content", "ContentProvider")
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
  (if component.getASupertype*().hasQualifiedName("android.content", "ContentProvider")
    then "Is a ContentProvider (potentially exposed by default in Android < 4.2). "
   else "") +
  (if isIntentTarget(component)
    then "Used as an Intent target. "
   else "") +
  (if isUsedInPendingIntent(component)
    then "Used in a PendingIntent. "
   else "") +
  "Verify if this exposure is intentional and properly secured."