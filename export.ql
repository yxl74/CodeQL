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

predicate isDeclaredInManifest(AndroidComponent component) {
  exists(component.getComponentXmlElement())
}

predicate isExplicitlyExported(AndroidComponent component) {
  exists(AndroidComponentXmlElement elem |
    elem = component.getComponentXmlElement() and
    elem.getAttributeValue("android:exported") = "true"
  )
}

predicate hasIntentFilter(AndroidComponent component) {
  exists(AndroidComponentXmlElement elem, XmlElement intentFilter |
    elem = component.getComponentXmlElement() and
    intentFilter.getParent() = elem and
    intentFilter.getName() = "intent-filter"
  )
}

predicate isDynamicallyRegisteredOrStarted(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().hasName([
      "registerReceiver", 
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
  or
  exists(MethodCall mc |
    (
      mc.getMethod().hasName("registerService")
      or
      mc.getMethod().hasName("addService") and
      mc.getMethod().getDeclaringType().hasQualifiedName("android.os", "ServiceManager")
    ) and
    (
      mc.getAnArgument().getType() = component
      or
      mc.getAnArgument().(VarAccess).getVariable().getType() = component
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

from AndroidComponent component
where
  isDeclaredInManifest(component)
  or
  isExplicitlyExported(component)
  or
  hasIntentFilter(component)
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
      isDeclaredInManifest(component) and
      reason = "Declared in the manifest. "
    ) or (
      isExplicitlyExported(component) and
      reason = "Explicitly exported in the manifest. "
    ) or (
      hasIntentFilter(component) and
      reason = "Has an intent filter in the manifest. "
    ) or (
      isDynamicallyRegisteredOrStarted(component) and
      reason = "Dynamically registered or started. "
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