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

  AndroidComponentXmlElement getComponentXmlElement() {
    result.getName() = this.getComponentType() and
    result.getAttributeValue("android:name") = this.getName()
  }

  string getComponentType() {
    this.getASupertype*().hasQualifiedName("android.app", "Activity") and result = "activity"
    or
    this.getASupertype*().hasQualifiedName("android.app", "Service") and result = "service"
    or
    this.getASupertype*().hasQualifiedName("android.content", "BroadcastReceiver") and result = "receiver"
    or
    this.getASupertype*().hasQualifiedName("android.content", "ContentProvider") and result = "provider"
  }
}

predicate isDynamicallyRegisteredOrStarted(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().hasName([
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
      mc.getAnArgument().getType() = component
      or
      mc.getAnArgument().(VarAccess).getVariable().getType() = component
    )
  )
}

predicate isDynamicallyRegisteredAndExported(AndroidComponent component) {
  exists(MethodCall mc, Expr flagArg |
    mc.getMethod().hasName(["registerReceiver", "registerContentProvider"]) and
    mc.getAnArgument().getType() = component and
    flagArg = mc.getArgument(mc.getNumArgument() - 1) and  // Assuming the last argument is the flags
    (
      flagArg.(IntegerLiteral).getValue().bitAnd(1) != 0  // RECEIVER_EXPORTED = 1 << 0
      or
      flagArg.(BinaryExpr).getAnOperand().(IntegerLiteral).getValue().bitAnd(1) != 0
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
  exists(MethodCall mc |
    mc.getMethod().getDeclaringType().hasQualifiedName("android.app", "PendingIntent") and
    mc.getAnArgument().getType() = component
  )
}

predicate isExported(AndroidComponent component) {
  exists(AndroidComponentXmlElement elem |
    elem = component.getComponentXmlElement() and
    (
      elem.getAttributeValue("android:exported") = "true"
      or
      (
        not elem.getAttributeValue("android:exported") = "false" and
        exists(XmlElement intentFilter |
          intentFilter.getParent() = elem and
          intentFilter.getName() = "intent-filter"
        )
      )
    )
  )
  or
  isDynamicallyRegisteredAndExported(component)
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
select 
  component,
  "This component is potentially exposed to external interactions. Reason: " +
  concat(string reason |
    (
      isExported(component) and
      reason = "Explicitly exported in the manifest, has an intent filter without android:exported=\"false\", or dynamically registered as exported. "
    ) or (
      isDynamicallyRegisteredOrStarted(component) and not isDynamicallyRegisteredAndExported(component) and
      reason = "Potentially dynamically registered or started (but not explicitly as exported). "
    ) or (
      component.getASupertype*().hasQualifiedName("android.content", "ContentProvider") and
      reason = "Is a ContentProvider (potentially exposed by default in Android < 4.2). "
    ) or (
      isIntentTarget(component) and
      reason = "Used as an Intent target. "
    ) or (
      isUsedInPendingIntent(component) and
      reason = "Used in a PendingIntent. "
    )
    |
    reason
  ) +
  "Verify if this exposure is intentional and properly secured."