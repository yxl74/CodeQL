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
    or
    this.getAnAncestor().hasQualifiedName("android.os", "Binder")
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
    or
    this.getAnAncestor().hasQualifiedName("android.os", "Binder") and result = "binder"
  }
}

predicate isExportedInManifest(AndroidComponent component) {
  exists(AndroidComponentXmlElement elem |
    elem = component.getComponentXmlElement() and
    (
      elem.getAttributeValue("android:exported") = "true"
      or
      (
        not exists(elem.getAttributeValue("android:exported")) and
        (
          component instanceof AndroidContentProvider // Content providers are exported by default in Android < 4.2
          or
          exists(XmlElement intentFilter |
            intentFilter.getParent() = elem and
            intentFilter.getName() = "intent-filter"
          )
        )
      )
    )
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
}

predicate isRegisteredWithServiceManager(AndroidComponent component) {
  exists(MethodCall mc |
    mc.getMethod().hasName("addService") and
    mc.getMethod().getDeclaringType().hasQualifiedName("android.os", "ServiceManager") and
    (
      mc.getArgument(1).getType() = component
      or
      mc.getArgument(1).(VarAccess).getVariable().getType() = component
      or
      exists(CastExpr ce |
        ce = mc.getArgument(1) and
        ce.getExpr().getType() = component
      )
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
  isExportedInManifest(component)
  or
  isDynamicallyRegisteredOrStarted(component)
  or
  isRegisteredWithServiceManager(component)
  or
  isIntentTarget(component)
  or
  isUsedInPendingIntent(component)
select 
  component,
  "This component is potentially exposed to external interactions. Reason: " +
  concat(string reason |
    (
      isExportedInManifest(component) and
      reason = "Exported in the manifest (explicitly or implicitly due to intent filter or being a ContentProvider). "
    ) or (
      isDynamicallyRegisteredOrStarted(component) and
      reason = "Dynamically registered or started. "
    ) or (
      isRegisteredWithServiceManager(component) and
      reason = "Registered with ServiceManager.addService. "
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